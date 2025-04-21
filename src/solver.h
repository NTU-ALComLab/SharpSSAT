/*
 * solver.h
 *
 *  Created on: Aug 23, 2012
 *      Author: marc
 */

#ifndef SOLVER_H_
#define SOLVER_H_

#include "strategy.h"
#include "basic_types.h"
#include "instance.h"
#include "component_management.h"


enum retStateT {
  EXIT, RESOLVED, PROCESS_COMPONENT, BACKTRACK
};

enum StateName {
  STATE_NIL,

  // denotes that the formula has been found to be unsatisfiable
  STATE_UNSAT,

  // a literal has been asserted --> perform BCP
  // the literal and its antecedent are set
  STATE_ASSERTION_PENDING,

  // the current decision level has another yet unprocessed component
  STATE_PROCESS_COMPONENT,

  // denotes that the remaining formula has been found
  STATE_SOLUTION_FOUND,
  
  // a conflict has been found and has to be resolved
  // via clause learning and backtracking
  STATE_CONFLICT,

  STATE_SUCCESS,

  STATE_TIMEOUT,

  STATE_ABORTED
};

struct SolverState {
  StateName name;
  // if the state name is CONFLICT,
  // then violated_clause contains the clause determining the conflict;
  vector<LiteralID> violated_clause;
};





class Solver: public Instance {
public:
  Solver() {
    stopwatch_.setTimeBound(config_.time_bound_seconds);
  }

  ~Solver() {
    delete trace_;
  }

  bool solve(const string & file_name);
  void generateStrategy(const string & file_name);
  void generateExistStrategy(const string & file_name);
  void generateUnivStrategy(const string & file_name);
  void generateDNNF(const string & file_name);
  void generateCertificate(const string & up, const string & low, const string & prob);

  SolverConfiguration &config() {
    return config_;
  }

  void setTimeBound(long int i) {
    stopwatch_.setTimeBound(i);
  }
  void setDNNFName(const string& s) {
    DNNF_filename_ = s;
  }

private:
  SolverState state_;
  SolverConfiguration config_;

  DecisionStack stack_; // decision stack
  vector<LiteralID> literal_stack_;

  StopWatch stopwatch_;

  ComponentAnalyzer component_analyzer_ = ComponentAnalyzer(config_,statistics_,literal_values_);

  // vector<double> td_score_;

  // the last time conflict clauses have been deleted
  unsigned long last_ccl_deletion_time_ = 0;
  // the last time the conflict clause storage has been compacted
  unsigned long last_ccl_cleanup_time_ = 0;

  Trace*        trace_ = nullptr;
  ofstream      out_file_;      // output strategy file
  vector<int>   exist_imp_;     // temp vec holding exist implication literals
  vector<int>   univ_imp_;      // temp vec holding universal implication literals
  vector<int>   random_imp_;    // temp vec holding random implication literals
  string        DNNF_filename_; // output dec-DNNF filname

  bool simplePreProcess();
  bool prepFailedLiteralTest();
  // we assert that the formula is consistent
  // and has not been found UNSAT yet
  // hard wires all assertions in the literal stack into the formula
  // removes all set variables and essentially reinitiallizes all
  // further data


  void HardWireAndCompact();

  SOLVER_StateT countSAT();

  void decideLiteral();
  bool bcp();

  ///  this method performs Failed literal tests online
  bool implicitBCP();

  // this is the actual BCP algorithm
  // starts propagating all literal in literal_stack_
  // beginingg at offset start_at_stack_ofs
  bool BCP(unsigned start_at_stack_ofs);

  retStateT backtrack();

  // if on the current decision level
  // a second branch can be visited, RESOLVED is returned
  // otherwise returns BACKTRACK
  retStateT resolveConflict();


  // begin SSAT
  SOLVER_StateT countSSAT();
  bool ssatDecideLiteral();

  // SSAT strategy generation
  void initializeBLIF(ofstream&);
  void finalizeBLIF(ofstream&);
  void initializeExistBLIF(ofstream&);
  void initializeUnivBLIF(ofstream&);
  void finalizeExistBLIF(ofstream&);
  void finalizeUnivBLIF(ofstream&);

  /////////////////////////////////////////////
   //  BEGIN small helper functions
   /////////////////////////////////////////////

  float scoreOf(VariableIndex v) {
    float score = 0;
    if (config_.vsads_freq){
      score = component_analyzer_.scoreOf(v);
    }
    if (config_.vsads_act){
      score += 10.0*literal(LiteralID(v, true)).activity_score_;
      score += 10.0*literal(LiteralID(v, false)).activity_score_;
    }

    return score;
  }

  bool setLiteralIfFree(LiteralID lit,
      Antecedent ant = Antecedent(NOT_A_CLAUSE)) {
    if (literal_values_[lit] != X_TRI)
      return false;
    var(lit).decision_level = stack_.get_decision_level();
    var(lit).ante = ant;
    literal_stack_.push_back(lit);
    if (ant.isAClause() && ant.asCl() != NOT_A_CLAUSE)
      getHeaderOf(ant.asCl()).increaseActivity();
    literal_values_[lit] = T_TRI;
    literal_values_[lit.neg()] = F_TRI;
    return true;
  }
  bool repeatedPureLiteral(LiteralID lit){
    return var(lit).decision_level == stack_.get_decision_level() && var(lit).ante.asCl() == NOT_A_CLAUSE && literal_values_[lit] == T_TRI && literal_values_[lit.neg()] == F_TRI;
  }

  void setPureLiteralsOnTrace()
  {
    Node* node = stack_.top().getNode();
    const vector<int>& pureLits = node->getPureLiterals();
    for (auto lit : pureLits)
      assert (setLiteralIfFree( LiteralID(lit) ) || repeatedPureLiteral( LiteralID(lit)) );
  }


  void printOnlineStats();

  void print(vector<LiteralID> &vec);
  void print(vector<unsigned> &vec);

  void setState(StateName name) {
    state_.name = name;
  }

  void setConflictState(LiteralID litA, LiteralID litB) {
    state_.violated_clause.clear();
    state_.violated_clause.push_back(litA);
    state_.violated_clause.push_back(litB);
    state_.name = STATE_CONFLICT;
  }
  void setConflictState(ClauseOfs cl_ofs) {
    getHeaderOf(cl_ofs).increaseActivity();
    state_.violated_clause.clear();
    for (auto it = beginOf(cl_ofs); *it != SENTINEL_LIT; it++)
      state_.violated_clause.push_back(*it);
    state_.name = STATE_CONFLICT;
  }

  void setConflictState(LiteralID lit){
    state_.violated_clause.clear();
    state_.violated_clause.push_back(lit);
    state_.name = STATE_CONFLICT;
  }

  vector<LiteralID>::const_iterator TOSLiteralsBegin() {
    return literal_stack_.begin() + stack_.top().literal_stack_ofs();
  }

  void initStack(unsigned int resSize) {
    stack_.clear();
    stack_.reserve(resSize);
    literal_stack_.clear();
    literal_stack_.reserve(resSize);
    // initialize the stack to contain at least level zero
    stack_.push_back(StackLevel(1, 0, 2));
    stack_.back().changeBranch();
  }

  // will be called only after preprocessing
  void initTrace(){
    delete trace_;
    Node* n = new Node(DUMMY);
    Node* zero = new Node(DUMMY);
    Node* one = new Node(DUMMY);
    stack_.back().setNode(n);
    n->changeBranch();
    trace_ = new Trace(n, zero, one); // n is the single source
  }

  const LiteralID &TOS_decLit() {
    assert(stack_.top().literal_stack_ofs() <  literal_stack_.size());
    return literal_stack_[stack_.top().literal_stack_ofs()];
  }

  // NOTE
  // reset implication here
  void reactivateTOS() {
    for (auto it = TOSLiteralsBegin(); it != literal_stack_.end(); it++)
      unSet(*it);
    component_analyzer_.cleanRemainingComponentsOf(stack_.top());
    literal_stack_.resize(stack_.top().literal_stack_ofs());
    stack_.top().resetRemainingComps();
    //NOTE for ssat
  }


  /////////////////////////////////////////////
  //  BEGIN conflict analysis
  /////////////////////////////////////////////

  // this is an array of all the clauses found
  // during the most recent conflict analysis
  // it might contain more than 2 clauses
  // but always will have:
  //      uip_clauses_.front() the 1UIP clause found
  //      uip_clauses_.back() the lastUIP clause found
  //  possible clauses in between will be other UIP clauses
  vector<vector<LiteralID> > uip_clauses_;

  // the assertion level of uip_clauses_.back()
  // or (if the decision variable did not have an antecedent
  // before) then assertionLevel_ == DL;
  int assertion_level_ = 0;

  double assert_prob_ = 1; // level 0 implication
  // build conflict clauses from most recent conflict
  // as stored in state_.violated_clause
  // solver state must be CONFLICT to work;
  // this first method record only the last UIP clause
  // so as to create clause that asserts the current decision
  // literal
  void recordLastUIPCauses();
  void recordAllUIPCauses();

  void minimizeAndStoreUIPClause(LiteralID uipLit,
      vector<LiteralID> & tmp_clause, bool seen[]);
  void storeUIPClause(LiteralID uipLit, vector<LiteralID> & tmp_clause);
  int getAssertionLevel() const {
    return assertion_level_;
  }

  /////////////////////////////////////////////
  //  END conflict analysis
  /////////////////////////////////////////////
};




#endif /* SOLVER_H_ */
