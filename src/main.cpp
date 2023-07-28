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

int main(int argc, char *argv[]) {

  string input_file;
  Solver theSolver;

  if (argc <= 1) {
    cout << "Usage: SharpSSAT [options] [SDIMACS_File]" << endl;
    cout << "Options: " << endl;
    // cout << "\t -noPP  \t turn off preprocessing" << endl;
    //cout << "\t -noNCB \t turn off nonchronological backtracking" << endl;
    cout << "\t -q       \t quiet mode" << endl;
    cout << "\t -t [s]   \t set time bound to s seconds" << endl;
    cout << "\t -noCC    \t turn off component caching" << endl;
    cout << "\t -noCL    \t turn off clause learning" << endl;
    cout << "\t -cs [n]  \t set max cache size to n MB" << endl;
    cout << "\t -s       \t ssat solving" << endl;
    cout << "\t -p       \t turn on pure literal detection" << endl;
    cout << "\t -c       \t turn on pure component detection" << endl;
    cout << "\t -k       \t turn on strategy generation"  << endl;
    cout << "\t -d [file]\t turn on dec-DNNF writing"  << endl;
    cout << "\t" << endl;

    return -1;
  }

  for (int i = 1; i < argc; i++) {
//    if (strcmp(argv[i], "-noNCB") == 0)
//      theSolver.config().perform_non_chron_back_track = false;
    if ( strcmp(argv[i], "-k")==0 )
      theSolver.config().strategy_generation = true;
    else if ( strcmp(argv[i], "-d")==0 ) {
        theSolver.config().compile_DNNF = true;
        if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      theSolver.setDNNFName(argv[i + 1]);
      ++i;
    }
    else if ( strcmp(argv[i], "-c")==0 )
      theSolver.config().perform_pure_component = true;
    else if ( strcmp(argv[i], "-p")==0 )
      theSolver.config().perform_pure_literal = true;
    else if ( strcmp(argv[i], "-s")==0 )
      theSolver.config().ssat_solving = true;
    else if (strcmp(argv[i], "-noCC") == 0)
      theSolver.config().perform_component_caching = false;
    else if (strcmp(argv[i], "-noCL") == 0)
      theSolver.config().perform_clause_learning= false;
    else if (strcmp(argv[i], "-q") == 0)
      SolverConfiguration::quiet = true;
    else if (strcmp(argv[i], "-verbose") == 0)
      theSolver.config().verbose = true;
    else if (strcmp(argv[i], "-t") == 0) {
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      theSolver.config().time_bound_seconds = atol(argv[i + 1]);
      if (theSolver.config().verbose)
        cout << "time bound set to" << theSolver.config().time_bound_seconds << "s\n";
    } else if (strcmp(argv[i], "-cs") == 0) {
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      theSolver.config().maximum_cache_size_bytes = atol(argv[i + 1]) * 1000000;
    } else
      input_file = argv[i];
  }

  theSolver.solve(input_file);
  if(theSolver.config().strategy_generation){
    string output_file = regex_replace(input_file, regex("[.]sdimacs"), ".blif");
    cout << "strategy written to " << output_file << endl;
    theSolver.generateStrategy(output_file);
  }
  return 0;
}
