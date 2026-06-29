//    sharpSAT
//    Copyright (C) 2012  Marc Thurley
//
//    This program is free software: you can redistribute it and/or modify
//    it under the terms of the GNU General Public License as published by
//    the Free Software Foundation, either version 3 of the License, or
//    (at your option) any later version.
//
//    This program is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//    GNU General Public License for more details.
//
//    You should have received a copy of the GNU General Public License
//    along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "solver.h"

#include <iostream>
#include <regex>


using namespace std;


template <typename T_Prob>
int run_solver(SolverConfiguration& config, const string& input_file);


int main(int argc, char *argv[]) {
  if (argc <= 1) {
    cout << "usage: SharpSSAT [options] SDIMACS_File" << endl;
    cout << "options: " << endl;
    // cout << "  -noPP  \t turn off preprocessing" << endl;
    // cout << "  -noNCB \t turn off nonchronological backtracking" << endl;
    cout << "  -q       \t quiet mode" << endl;
    cout << "  -t [s]   \t set time bound to s seconds" << endl;
    cout << "  -noCC    \t turn off component caching" << endl;
    cout << "  -noCL    \t turn off clause learning" << endl;
    cout << "  -cs [n]  \t set max cache size to n MB" << endl;
    cout << "  -s       \t ssat solving" << endl;
    cout << "  -p       \t turn on pure literal detection" << endl;
    cout << "  -c       \t turn on pure component detection" << endl;
    cout << "  -k       \t turn on strategy generation"  << endl;
    cout << "  -u       \t enable universal quatifiers"  << endl;
    cout << "  -d [file]\t turn on dec-DNNF writing"  << endl;
    cout << "  -l       \t turn on certficate generation"  << endl;
    cout << "  -mp      \t use mpq rational number" << endl;

    return -1;
  }

  string input_file;
  SolverConfiguration config;
  bool use_mpq = false;

  for (int i = 1; i < argc; i++) {
    // if (strcmp(argv[i], "-noNCB") == 0)
    //   config.perform_non_chron_back_track = false;
    if ( strcmp(argv[i], "-k")==0 )
      config.strategy_generation = true;
    else if ( strcmp(argv[i], "-l")==0 )
      config.certificate_generation = true;
    else if ( strcmp(argv[i], "-d")==0 ) {
      config.compile_DNNF = true;
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      config.DNNF_filename = argv[i + 1];
      ++i;
    }
    if ( strcmp(argv[i], "-c")==0 )
      config.perform_pure_component = true;
    if ( strcmp(argv[i], "-p")==0 )
      config.perform_pure_literal = true;
    if ( strcmp(argv[i], "-s")==0 )
      config.ssat_solving = true;
    if (strcmp(argv[i], "-mp") == 0)
      use_mpq = true;
    if (strcmp(argv[i], "-noCC") == 0)
      config.perform_component_caching = false;
    if (strcmp(argv[i], "-noCL") == 0)
      config.perform_clause_learning= false;
    else if (strcmp(argv[i], "-q") == 0)
      SolverConfiguration::quiet = true;
    else if (strcmp(argv[i], "-verbose") == 0)
      config.verbose = true;
    else if (strcmp(argv[i], "-u") == 0)
      config.include_forall = true;
    else if (strcmp(argv[i], "-t") == 0) {
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      config.time_bound_seconds = atol(argv[i + 1]);
      if (config.verbose)
        cout << "time bound set to" << config.time_bound_seconds << "s\n";
    }
    else if (strcmp(argv[i], "-cs") == 0) {
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      config.maximum_cache_size_bytes = atol(argv[i + 1]) * 1000000;
    }
    else
      input_file = argv[i];
  }

  if (config.include_forall && (config.certificate_generation || config.compile_DNNF)) {
    cout << "Knowledge compilation with universal quantifiers is not supported at the moment" << endl;
    return -1;
  }

  if (use_mpq) {
    return run_solver<mpq_class>(config, input_file);
  }
  else {
    return run_solver<double>(config, input_file);
  }
}


template <typename T_Prob>
int run_solver(SolverConfiguration& config, const string& input_file) {
  Solver<T_Prob> theSolver;
  theSolver.config() = config;
  if (!theSolver.solve(input_file)) return -1;
  if(theSolver.config().strategy_generation){
    #ifdef DEBUG_TRACE
      theSolver.printTrace();
    #endif
    if(theSolver.config().include_forall){
      string output_file_exist = regex_replace(input_file, regex("[.]sdimacs"), "_exist.blif");
      cout << "existential strategy written to " << output_file_exist << endl;
      theSolver.generateExistStrategy(output_file_exist);
      string output_file_univ = regex_replace(input_file, regex("[.]sdimacs"), "_univ.blif");
      cout << "universal strategy written to " << output_file_univ << endl;
      theSolver.generateUnivStrategy(output_file_univ);
    }
    else{
      string output_file = regex_replace(input_file, regex("[.]sdimacs"), ".blif");
      cout << "strategy written to " << output_file << endl;
      theSolver.generateStrategy(output_file);
    }
  }
  if(theSolver.config().certificate_generation){
    string upTrace_file = regex_replace(input_file, regex("[.]sdimacs"), "_up.nnf");
    cout << "upper trace written to " << upTrace_file << endl;
    string lowTrace_file = regex_replace(input_file, regex("[.]sdimacs"), "_low.nnf");
    cout << "lower trace written to " << lowTrace_file << endl;
    string prob_file = regex_replace(input_file, regex("[.]sdimacs"), ".prob");
    cout << "maximum satisfying probability written to " << prob_file << endl;
    theSolver.generateCertificate(upTrace_file, lowTrace_file, prob_file);
  }
  return 0;
}
