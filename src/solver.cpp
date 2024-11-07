/*
 * solver.cpp
 *
 *  Created on: Aug 23, 2012
 *      Author: marc
 */
#include "solver.h"
#include <deque>

// extern string TmpInstance(int a, int b, int c, string tmp_dir) ;
// extern TreeDecomposition TreeDecompose(const Graph& graph, double time, string tmp_dir);

void Solver::print(vector<LiteralID> &vec) {
  for (auto l : vec)
    cout << l.toInt() << " ";
  cout << endl;
}

void Solver::print(vector<unsigned> &vec) {
  for (auto l : vec)
    cout << l << " ";
  cout << endl;
}

bool Solver::simplePreProcess() {
  if (!config_.perform_pre_processing)
    return true;
  assert(literal_stack_.size() == 0);
  unsigned start_ofs = 0;
//BEGIN process unit clauses
  for (auto lit : unit_clauses_){
    setLiteralIfFree(lit);
    if(literal_values_[lit] != T_TRI){
        return false;
    }
    stack_.top().includePathProb( prob(lit) );
    if(qType(lit)==EXISTENTIAL)
      exist_imp_.push_back(lit.toInt());
    else{
        assert(qType(lit) == RANDOM);
        random_imp_.push_back(lit.toInt());
    }
  }
//END process unit clauses
  bool succeeded = BCP(start_ofs);

  if (succeeded && !config_.ssat_solving)
    succeeded &= prepFailedLiteralTest();

  if (succeeded ){
    if (config_.ssat_solving){
      //FIXME
      double assert_prob_ = stack_.top().getCurPathProb();
      LiteralIndexedVector<TriValue> lv = LiteralIndexedVector<TriValue>(literal_values_);
      HardWireAndCompact();
      literal_values_ = lv;
      stack_.top().includePathProb(assert_prob_);
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        stack_.top().getNode()->recordExistImplications(exist_imp_);
        stack_.top().getNode()->recordRandomImplications(random_imp_);
      }
    }
    else
      HardWireAndCompact();
  }
  return succeeded;
}

bool Solver::prepFailedLiteralTest() {
  unsigned last_size;
  do {
    last_size = literal_stack_.size();
    for (unsigned v = 1; v < variables_.size(); v++)
      if (isActive(v)) {
        unsigned sz = literal_stack_.size();
        setLiteralIfFree(LiteralID(v, true));
        bool res = BCP(sz);
        while (literal_stack_.size() > sz) {
          unSet(literal_stack_.back());
          literal_stack_.pop_back();
        }

        if (!res) {
          sz = literal_stack_.size();
          setLiteralIfFree(LiteralID(v, false));
          if (!BCP(sz))
            return false;
        } else {

          sz = literal_stack_.size();
          setLiteralIfFree(LiteralID(v, false));
          bool resb = BCP(sz);
          while (literal_stack_.size() > sz) {
            unSet(literal_stack_.back());
            literal_stack_.pop_back();
          }
          if (!resb) {
            sz = literal_stack_.size();
            setLiteralIfFree(LiteralID(v, true));
            if (!BCP(sz))
              return false;
          }
        }
      }
  } while (literal_stack_.size() > last_size);

  return true;
}


void Solver::HardWireAndCompact() {
  compactClauses();
  if(!config_.ssat_solving)
    compactVariables();
  else{
    unit_clauses_.clear();
  }
  literal_stack_.clear();

  for (auto l = LiteralID(1, false); l != literals_.end_lit(); l.inc()) {
    literal(l).activity_score_ = literal(l).binary_links_.size() - 1;
    literal(l).activity_score_ += occurrence_lists_[l].size();
  }


  statistics_.num_unit_clauses_ = unit_clauses_.size();

  statistics_.num_original_binary_clauses_ = statistics_.num_binary_clauses_;
  statistics_.num_original_unit_clauses_ = statistics_.num_unit_clauses_ =
      unit_clauses_.size();
  initStack(num_variables());
  if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation)
    initTrace();
  original_lit_pool_size_ = literal_pool_.size();
}

void Solver::solve(const string &file_name) {
  stopwatch_.start();
  statistics_.input_file_ = file_name;

  createfromFile(file_name);
  initStack(num_variables());
  if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation)
    initTrace();

  if (!config_.quiet) {
    cout << "Solving " << file_name << endl;
    statistics_.printShortFormulaInfo();
  }
  if (!config_.quiet)
    cout << endl << "Preprocessing .." << flush;

  // SSAT must have preprocessing
  bool notfoundUNSAT = simplePreProcess();
  if (!config_.quiet)
    cout << " DONE" << endl;

  if (notfoundUNSAT) {
	  if(num_variables() == 0){
        // TODO: Check whether this is affected by HardWireAndCompact
		  statistics_.exit_state_ = SUCCESS;
		  statistics_.set_final_solution_count(1.0);
          if(config_.compile_DNNF || config_.certificate_generation){
            stack_.top().getNode()->addDescendant(trace_->getConstant(1));
          }
  }else{

    if (!config_.quiet) {
      statistics_.printShortFormulaInfo();
    }

    last_ccl_deletion_time_ = last_ccl_cleanup_time_ = statistics_.getTime();

    state_.violated_clause.reserve(num_variables());
    component_analyzer_.initialize(literals_, literal_pool_, var2Q_);


    statistics_.exit_state_ = config_.ssat_solving ? countSSAT() : countSAT();

    if(config_.ssat_solving){
      statistics_.set_final_solution_prob(assert_prob_*stack_.top().getTotalSatProb());
    }
    else{
      statistics_.set_final_solution_count(stack_.top().getTotalModelCount());
    }
    statistics_.num_long_conflict_clauses_ = num_conflict_clauses();
    statistics_.cache_bytes_memory_usage_ =
        component_analyzer_.cache().recompute_bytes_memory_usage();
	  }
  } else {
    statistics_.exit_state_ = SUCCESS;
    statistics_.set_final_solution_count(0.0);
    cout << endl << " FOUND UNSAT DURING PREPROCESSING " << endl;

    if(config_.compile_DNNF || config_.certificate_generation){
        stack_.top().getNode()->addDescendant(trace_->getConstant(0));
    }
  }
  cout << "End of Solving" << endl;
  if(config_.strategy_generation){
    cout << "Start Generating Strategy..." << endl;
    Node::resetGlobalVisited();
    statistics_.set_num_nodes(trace_->numNodes());
    statistics_.set_num_edges(trace_->numEdges());
  }
  else if(config_.compile_DNNF){
    cout << "Start Generating DNNF..." << endl;
    Node::resetGlobalVisited();
    statistics_.set_num_nodes(trace_->numNodes());
    statistics_.set_num_edges(trace_->numEdges());
    // TODO: change DNNF name
    generateDNNF(DNNF_filename_);
  }
  else if(config_.certificate_generation){
    cout << "Start Generating Certificate..." << endl;
    Node::resetGlobalVisited();
    statistics_.set_num_nodes(trace_->numNodes());
    statistics_.set_num_edges(trace_->numEdges());
  }
  stopwatch_.stop();
  statistics_.time_elapsed_ = stopwatch_.getElapsedSeconds();
  statistics_.writeToFile("data.out");
  if(!SolverConfiguration::quiet)
    statistics_.printShort();
}

SOLVER_StateT Solver::countSAT() {
  retStateT res = RESOLVED;

  while (true) {
    // assertion failed
    //assert(state_.name != STATE_ASSERTION_PENDING);
    while (component_analyzer_.findNextRemainingComponentOf(stack_.top())) {
      decideLiteral();
      if (stopwatch_.timeBoundBroken())
        return TIMEOUT;
      if (stopwatch_.interval_tick())
        printOnlineStats();

      while (!bcp()) {
        res = resolveConflict();
        if (res == BACKTRACK)
          break;
      }
      if (res == BACKTRACK)
        break;
      assert(state_.name != STATE_ASSERTION_PENDING);
    }

    res = backtrack();
    if (res == EXIT)
      return SUCCESS;
    while (res != PROCESS_COMPONENT && !bcp()) {
      res = resolveConflict();
      if (res == BACKTRACK) {
        res = backtrack();
        if (res == EXIT)
          return SUCCESS;
      }
    }
  }
  return SUCCESS;
}

//FIXME
SOLVER_StateT Solver::countSSAT() {
  retStateT res = RESOLVED;

  while (true) {
    //NOTE assertion failed
    //assert(state_.name != STATE_ASSERTION_PENDING);
    while (component_analyzer_.findNextRemainingComponentOf(stack_.top())) {
      setPureLiterals();
      ssatDecideLiteral();	// laurenl: increase stack level and create a new decision node set to the decided literal
      if (stopwatch_.timeBoundBroken())
        return TIMEOUT;
      if (stopwatch_.interval_tick())
        printOnlineStats();

      while (!bcp()) {
        res = resolveConflict();
        if (res == BACKTRACK)
          break;
      }
      if (res == BACKTRACK)
        break;
      assert(state_.name != STATE_ASSERTION_PENDING);
    }
    if(config_.compile_DNNF || config_.certificate_generation){
        Node* node = stack_.top().getNode();
        if(node->empty(config_.certificate_generation)){
            node->addDescendant(trace_->getConstant(1));
        }
    }

    res = backtrack();
    if (res == EXIT)
      return SUCCESS;
    while (res != PROCESS_COMPONENT && !bcp()) {
      res = resolveConflict();
      if (res == BACKTRACK) {
        res = backtrack();
        if (res == EXIT)
          return SUCCESS;
      }
    }
  }
  return SUCCESS;
}

void Solver::decideLiteral() {
  // establish another decision stack level
  stack_.push_back(
      StackLevel(stack_.top().currentRemainingComponent(),
          literal_stack_.size(), component_analyzer_.component_stack_size()));
  float max_score = -1;
  float score;
  unsigned max_score_var = 0;
  for (auto it = component_analyzer_.superComponentOf(stack_.top()).varsBegin();
      *it != varsSENTINEL; it++) {
    score = scoreOf(*it);
    if (score > max_score) {
      max_score = score;
      max_score_var = *it;
    }
  }
  // this assert should always hold,
  // if not then there is a bug in the logic of countSAT();
  assert(max_score_var != 0);

  LiteralID theLit(max_score_var,
      literal(LiteralID(max_score_var, true)).activity_score_
          > literal(LiteralID(max_score_var, false)).activity_score_);
  setLiteralIfFree(theLit);
  setState(STATE_ASSERTION_PENDING);
  statistics_.num_decisions_++;

  if (statistics_.num_decisions_ % 128 == 0)
    decayActivities();

  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());
}

bool Solver::ssatDecideLiteral() {
  // establish another decision stack level
  // cout << "New Stack " << stack_.size() << ", Comp " << stack_.top().currentRemainingComponent() << endl;
  stack_.push_back(
      StackLevel(stack_.top().currentRemainingComponent(),
          literal_stack_.size(), component_analyzer_.component_stack_size()));


  float max_score = -1;
  float score;
  unsigned max_score_var = 0;
  int max_score_lev = statistics_.num_qlev + 1 ;
  for (auto it = component_analyzer_.superComponentOf(stack_.top()).varsBegin();
      *it != varsSENTINEL; it++) {
    if( !isActive( LiteralID(*it, false) )) continue;
    score = scoreOf(*it);
    if( qlev(*it) < max_score_lev ){
      max_score = score;
      max_score_var = *it;
      max_score_lev = qlev(*it);
    }
    else if ( (score > max_score) && (qlev(*it) == max_score_lev) ) {
      max_score = score;
      max_score_var = *it;
      max_score_lev = qlev(*it);
    }
  }

  // this assert should always hold,
  // if not then there is a bug in the logic of countSAT();
  assert(max_score_var != 0);

  LiteralID theLit(max_score_var,
      literal(LiteralID(max_score_var, true)).activity_score_
          > literal(LiteralID(max_score_var, false)).activity_score_);

  setLiteralIfFree(theLit);

  setState(STATE_ASSERTION_PENDING);
  statistics_.num_decisions_++;

  if (statistics_.num_decisions_ % 128 == 0)
    decayActivities();

  //ssat NOTE
  Node* n  = new Node();
  stack_.top().setIsDecRandom( qType(theLit)==RANDOM );
  stack_.top().setDecProb( prob(theLit) );
  stack_.top().setIsInv( theLit.sign() );
  n->setDecVar(theLit.var(), qType(theLit)==RANDOM, theLit.sign());
  stack_.top().setNode(n);
  // cout << "Decide " << theLit.toInt() << endl;

  return true;
  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());
}

retStateT Solver::backtrack() {
  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());
  do {
    if (stack_.top().branch_found_unsat()){
      component_analyzer_.removeAllCachePollutionsOf(stack_.top());
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        Node* n = stack_.top().getNode();
        assert(n);
        n->removeAllDescendants(n->getCurrentBranch());
        n->addDescendant(trace_->getConstant(0));
      }
    }
    else if (stack_.top().anotherCompProcessible())
      return PROCESS_COMPONENT;

    // Force explore both branch if compile_DNNF is true and pure literal is not enabled
    if ( !stack_.top().isSecondBranch() && (stack_.top().needSecondBranch() || (config_.compile_DNNF && !config_.perform_pure_literal)) ) {
      LiteralID aLit = TOS_decLit();
      assert(stack_.get_decision_level() > 0);
      stack_.top().changeBranch();
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        assert(stack_.top().getNode());
        stack_.top().getNode()->changeBranch();
      }
      reactivateTOS();
      setLiteralIfFree(aLit.neg(), NOT_A_CLAUSE);
      setState(STATE_ASSERTION_PENDING);
      return RESOLVED;
    }
    // // Exist early termination: mark second branch as constant zero
    if (!stack_.top().isSecondBranch() && (config_.compile_DNNF || config_.certificate_generation)) {
        // assert(false);
        Node* node = stack_.top().getNode();
        node->changeBranch();
        node->addDescendant(trace_->getConstant(0));
        node->setHasEarlyReturn();
        node->setPrunedBranch( node->getCurrentBranch() );
    }
    // OTHERWISE:  backtrack further
    // NOTE for ssat
    if(config_.ssat_solving){
      double p = stack_.top().getTotalSatProb();
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        Node* n = stack_.top().getNode();
        assert(n);
        if(n->isExist()) {
          // cout << "Mark Max Branch " << stack_.top().maxProbBranch() << endl;
          n->markMaxBranch(stack_.top().maxProbBranch());
        }
      }
      component_analyzer_.cacheSatProbOf(stack_.top().super_component(), p, stack_.top().getNode());
    }
    else{
      component_analyzer_.cacheModelCountOf(stack_.top().super_component(),
        stack_.top().getTotalModelCount());
    }


    if (stack_.get_decision_level() <= 0)
      break;
    reactivateTOS();

    assert(stack_.size()>=2);
    // NOTE for ssat
    if(config_.ssat_solving){
      (stack_.end()-2)->includeSatProb(stack_.top().getTotalSatProb());
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        assert((stack_.end()-2)->getNode());
        assert(stack_.top().getNode());
        ((stack_.end()-2)->getNode())->addDescendant(stack_.top().getNode());
      }
    }
    else
      (stack_.end() - 2)->includeSolution(stack_.top().getTotalModelCount());
    stack_.pop_back();

    // step to the next component not yet processed
    if(config_.ssat_solving && config_.perform_thresholding){
      if( !stack_.top().needSecondBranch() && stack_.top().isSecondBranch()){
        if (stack_.get_decision_level() <= 0) break;
        reactivateTOS();
        (stack_.end()-2)->includeSatProb(stack_.top().getTotalSatProb());
        stack_.pop_back();
      }
      stack_.top().nextUnprocessedComponent();
    }
    else
      stack_.top().nextUnprocessedComponent();

    assert(
        stack_.top().remaining_components_ofs() < component_analyzer_.component_stack_size()+1);

  } while (stack_.get_decision_level() >= 0);
  return EXIT;
}

retStateT Solver::resolveConflict() {
  statistics_.num_conflicts_++;

  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());

  stack_.top().mark_branch_unsat();
  //BEGIN Backtracking
  // maybe the other branch had some solutions
  if (stack_.top().isSecondBranch()) {
    return BACKTRACK;
  }

  Antecedent ant(NOT_A_CLAUSE);
  if ( uip_clauses_.back().front() == TOS_decLit().neg() && config_.perform_clause_learning ) {
    assert(TOS_decLit().neg() == uip_clauses_.back()[0]);
    var(TOS_decLit().neg()).ante = addUIPConflictClause(uip_clauses_.back());
    ant = var(TOS_decLit()).ante;
  }
  assert(stack_.get_decision_level() > 0);
  assert(stack_.top().branch_found_unsat());

  // we do not have to remove pollutions here,
  // since conflicts only arise directly before
  // remaining components are stored
  // hence
  assert(
      stack_.top().remaining_components_ofs() == component_analyzer_.component_stack_size());

  stack_.top().changeBranch();
  (stack_.top().getNode())->changeBranch();
  LiteralID lit = TOS_decLit();
  reactivateTOS();
  setLiteralIfFree(lit.neg(), ant);
  setState(STATE_ASSERTION_PENDING);
//END Backtracking
  return RESOLVED;
}

bool Solver::bcp() {
  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());
  assert(state_.name == STATE_ASSERTION_PENDING);
// the asserted literal has been set, so we start
// bcp on that literal
  unsigned start_ofs = literal_stack_.size() - 1;

  if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
    exist_imp_.clear();
    random_imp_.clear();
  }

//BEGIN process unit clauses
  for (auto lit : unit_clauses_){
    // NOTE we may possibly assign a unit literal as decLit
    //      that falsifies the formula
    if(setLiteralIfFree(lit)){
      //cout << "assign unit clause" << endl;
      stack_.top().includePathProb( prob(lit) );
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        if(qType(lit)==EXISTENTIAL)
          exist_imp_.push_back(lit.toInt());
        else{
            assert(qType(lit) == RANDOM);
            random_imp_.push_back(lit.toInt());
        }
      }
    }
    else{
      //cout << "unit clause already assigned" << endl;
      if(literal_values_[lit]==F_TRI)
        cout << "Warning!! already unsat" << endl;
    }
  }
//END process unit clauses

  setState(STATE_NIL);
  bool bSucceeded = BCP(start_ofs);

  if (config_.perform_failed_lit_test && bSucceeded) {
    bSucceeded = implicitBCP();
  }
  

  if (!bSucceeded) {
    assert(state_.name == STATE_CONFLICT);
    recordLastUIPCauses();

    if (statistics_.num_clauses_learned_ - last_ccl_deletion_time_
        > statistics_.clause_deletion_interval()) {
      deleteConflictClauses();
      last_ccl_deletion_time_ = statistics_.num_clauses_learned_;
    }

    if (statistics_.num_clauses_learned_ - last_ccl_cleanup_time_ > 100000) {
      compactConflictLiteralPool();
      last_ccl_cleanup_time_ = statistics_.num_clauses_learned_;
    }
  }

  if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
    if(bSucceeded){
      Node* n = stack_.top().getNode();
      n->recordExistImplications(exist_imp_);
      n->recordRandomImplications(random_imp_);
    }
    else{
        stack_.top().getNode()->addDescendant(trace_->getConstant(0));
    }
  }

  return bSucceeded;
}

//TODO include path prob into stack_.top
bool Solver::BCP(unsigned start_at_stack_ofs) {
  for (unsigned int i = start_at_stack_ofs; i < literal_stack_.size(); i++) {
    LiteralID unLit = literal_stack_[i].neg();
    //BEGIN Propagate Bin Clauses
    for (auto bt = literal(unLit).binary_links_.begin(); *bt != SENTINEL_LIT;
        bt++) {
      if (isResolved(*bt)) {
        setConflictState(unLit, *bt);
        return false;
      }
      if(setLiteralIfFree(*bt, Antecedent(unLit))){
        stack_.top().includePathProb( prob(*bt) );
        if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
          if(qType(*bt)==EXISTENTIAL){
            exist_imp_.push_back( (*bt).toInt() );
          }
          else{
            assert(qType(*bt) == RANDOM);
            random_imp_.push_back( (*bt).toInt() );
          }
        };
      }
    }
    //END Propagate Bin Clauses

    for (auto itcl = literal(unLit).watch_list_.rbegin(); *itcl != SENTINEL_CL;
        itcl++) {
      bool isLitA = (*beginOf(*itcl) == unLit);
      auto p_watchLit = beginOf(*itcl) + 1 - isLitA;
      auto p_otherLit = beginOf(*itcl) + isLitA;

      if (isSatisfied(*p_otherLit))
        continue;
      auto itL = beginOf(*itcl) + 2;
      while (isResolved(*itL))
        itL++;
      // either we found a free or satisfied lit
      if (*itL != SENTINEL_LIT) {
        literal(*itL).addWatchLinkTo(*itcl);
        swap(*itL, *p_watchLit);
        *itcl = literal(unLit).watch_list_.back();
        literal(unLit).watch_list_.pop_back();
      } else {
        // or p_unLit stays resolved
        // and we have hence no free literal left
        // for p_otherLit remain poss: Active or Resolved
        if (setLiteralIfFree(*p_otherLit, Antecedent(*itcl))) { // implication
          stack_.top().includePathProb( prob(*p_otherLit) );
          if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
            if(qType(*p_otherLit)==EXISTENTIAL){
              exist_imp_.push_back( (*p_otherLit).toInt() );
            }
            else{
                assert(qType(*p_otherLit) == RANDOM);
                random_imp_.push_back( (*p_otherLit).toInt() );
            }
          }
          if (isLitA)
            swap(*p_otherLit, *p_watchLit);
        } else {
          setConflictState(*itcl);
          return false;
        }
      }
    }
  }
  return true;
}

bool Solver::implicitBCP() {
  static vector<LiteralID> test_lits(num_variables());
  static LiteralIndexedVector<unsigned char> viewed_lits(num_variables() + 1,
      0);

  unsigned stack_ofs = stack_.top().literal_stack_ofs();
  while (stack_ofs < literal_stack_.size()) {
    test_lits.clear();
    for (auto it = literal_stack_.begin() + stack_ofs;
        it != literal_stack_.end(); it++) {
      for (auto cl_ofs : occurrence_lists_[it->neg()])
        if (!isSatisfied(cl_ofs)) {
          for (auto lt = beginOf(cl_ofs); *lt != SENTINEL_LIT; lt++)
            if (isActive(*lt) && !viewed_lits[lt->neg()]) {
              test_lits.push_back(lt->neg());
              viewed_lits[lt->neg()] = true;

            }
        }
    }

    stack_ofs = literal_stack_.size();
    for (auto jt = test_lits.begin(); jt != test_lits.end(); jt++)
      viewed_lits[*jt] = false;

    for (auto lit : test_lits)
      if (isActive(lit)) {
        unsigned sz = literal_stack_.size();
        // we increase the decLev artificially
        // s.t. after the tentative BCP call, we can learn a conflict clause
        // relative to the assignment of *jt
        stack_.startFailedLitTest();
        setLiteralIfFree(lit);

        assert(!hasAntecedent(lit));

        bool bSucceeded = BCP(sz);
        if (!bSucceeded)
          recordAllUIPCauses();

        stack_.stopFailedLitTest();

        while (literal_stack_.size() > sz) {
          unSet(literal_stack_.back());
          literal_stack_.pop_back();
        }

        if (!bSucceeded) {
          sz = literal_stack_.size();
          for (auto it = uip_clauses_.rbegin(); it != uip_clauses_.rend();
              it++) {
            setLiteralIfFree(it->front(), addUIPConflictClause(*it));
          }
          if (!BCP(sz))
            return false;
        }
      }
  }
  return true;
}

///////////////////////////////////////////////////////////////////////////////////////////////
// BEGIN module conflictAnalyzer
///////////////////////////////////////////////////////////////////////////////////////////////

void Solver::minimizeAndStoreUIPClause(LiteralID uipLit,
    vector<LiteralID> & tmp_clause, bool seen[]) {
  static deque<LiteralID> clause;
  clause.clear();
  assertion_level_ = -1;
  for (auto lit : tmp_clause) {
    if (existsUnitClauseOf(lit.var()))
      continue;
    bool resolve_out = false;
    if (hasAntecedent(lit)) {
      resolve_out = true;
      if (getAntecedent(lit).isAClause()) {
        for (auto it = beginOf(getAntecedent(lit).asCl()) + 1;
            *it != SENTINEL_CL; it++)
          if (!seen[it->var()]) {
            resolve_out = false;
            break;
          }
      } else if (!seen[getAntecedent(lit).asLit().var()]) {
        resolve_out = false;
      }
    }

    if (!resolve_out) {
      // uipLit should be the sole literal of this Decision Level
      if (var(lit).decision_level >= assertion_level_) {
        assertion_level_ = var(lit).decision_level;
        clause.push_front(lit);
      } else
        clause.push_back(lit);
    }
  }

  assert(var(uipLit).decision_level== stack_.get_decision_level());

  clause.push_front(uipLit);
  uip_clauses_.push_back(vector<LiteralID>(clause.begin(), clause.end()));
}

void Solver::recordLastUIPCauses() {
// note:
// variables of lower dl: if seen we dont work with them anymore
// variables of this dl: if seen we incorporate their
// antecedent and set to unseen
  assert(state_.name == STATE_CONFLICT);

  bool seen[num_variables() + 1];
  memset(seen, false, sizeof(bool) * (num_variables() + 1));

  static vector<LiteralID> tmp_clause;
  tmp_clause.clear();

  assertion_level_ = -1;
  uip_clauses_.clear();

  unsigned lit_stack_ofs = literal_stack_.size();
  int DL = stack_.get_decision_level();
  unsigned lits_at_current_dl = 0;

  for (auto l : state_.violated_clause) {
    if (var(l).decision_level == 0 || existsUnitClauseOf(l.var()))
      continue;
    if (var(l).decision_level < DL)
      tmp_clause.push_back(l);
    else
      lits_at_current_dl++;
    literal(l).increaseActivity();
    seen[l.var()] = true;
  }

  LiteralID curr_lit;
  while (lits_at_current_dl) {
    assert(lit_stack_ofs != 0);
    curr_lit = literal_stack_[--lit_stack_ofs];

    if (!seen[curr_lit.var()])
      continue;

    seen[curr_lit.var()] = false;

    if (lits_at_current_dl-- == 1) {
      // perform UIP stuff
      if (!hasAntecedent(curr_lit)) {
        // this should be the decision literal when in first branch
        // or it is a literal decided to explore in failed literal testing
        //assert(stack_.TOS_decLit() == curr_lit);
        break;
      }
    }

    assert(hasAntecedent(curr_lit));

    if (getAntecedent(curr_lit).isAClause()) {
      updateActivities(getAntecedent(curr_lit).asCl());
      assert(curr_lit == *beginOf(getAntecedent(curr_lit).asCl()));

      for (auto it = beginOf(getAntecedent(curr_lit).asCl()) + 1;
          *it != SENTINEL_CL; it++) {
        if (seen[it->var()] || var(*it).decision_level == 0
            || existsUnitClauseOf(it->var()))
          continue;
        if (var(*it).decision_level < DL)
          tmp_clause.push_back(*it);
        else
          lits_at_current_dl++;
        seen[it->var()] = true;
      }
    } else {
      LiteralID alit = getAntecedent(curr_lit).asLit();
      literal(alit).increaseActivity();
      literal(curr_lit).increaseActivity();
      if (!seen[alit.var()] && !var(alit).decision_level == 0
          && !existsUnitClauseOf(alit.var())) {
        if (var(alit).decision_level < DL)
          tmp_clause.push_back(alit);
        else
          lits_at_current_dl++;
        seen[alit.var()] = true;
      }
    }
  }

  minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);

  if (var(curr_lit).decision_level > assertion_level_)
    assertion_level_ = var(curr_lit).decision_level;
}

void Solver::recordAllUIPCauses() {
// note:
// variables of lower dl: if seen we dont work with them anymore
// variables of this dl: if seen we incorporate their
// antecedent and set to unseen

  assert(state_.name == STATE_CONFLICT);

  bool seen[num_variables() + 1];
  memset(seen, false, sizeof(bool) * (num_variables() + 1));

  static vector<LiteralID> tmp_clause;
  tmp_clause.clear();

  assertion_level_ = -1;
  uip_clauses_.clear();

  unsigned lit_stack_ofs = literal_stack_.size();
  int DL = stack_.get_decision_level();
  unsigned lits_at_current_dl = 0;

  for (auto l : state_.violated_clause) {
    if (var(l).decision_level == 0 || existsUnitClauseOf(l.var()))
      continue;
    if (var(l).decision_level < DL)
      tmp_clause.push_back(l);
    else
      lits_at_current_dl++;
    literal(l).increaseActivity();
    seen[l.var()] = true;
  }
  unsigned n = 0;
  LiteralID curr_lit;
  while (lits_at_current_dl) {
    assert(lit_stack_ofs != 0);
    curr_lit = literal_stack_[--lit_stack_ofs];

    if (!seen[curr_lit.var()])
      continue;

    seen[curr_lit.var()] = false;

    if (lits_at_current_dl-- == 1) {
      n++;
      if (!hasAntecedent(curr_lit)) {
        // this should be the decision literal when in first branch
        // or it is a literal decided to explore in failed literal testing
        //assert(stack_.TOS_decLit() == curr_lit);
        break;
      }
      // perform UIP stuff
      minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
    }

    assert(hasAntecedent(curr_lit));

    if (getAntecedent(curr_lit).isAClause()) {
      updateActivities(getAntecedent(curr_lit).asCl());
      assert(curr_lit == *beginOf(getAntecedent(curr_lit).asCl()));

      for (auto it = beginOf(getAntecedent(curr_lit).asCl()) + 1;
          *it != SENTINEL_CL; it++) {
        if (seen[it->var()] || var(*it).decision_level == 0
            || existsUnitClauseOf(it->var()))
          continue;
        if (var(*it).decision_level < DL)
          tmp_clause.push_back(*it);
        else
          lits_at_current_dl++;
        seen[it->var()] = true;
      }
    } else {
      LiteralID alit = getAntecedent(curr_lit).asLit();
      literal(alit).increaseActivity();
      literal(curr_lit).increaseActivity();
      if (!seen[alit.var()] && !var(alit).decision_level == 0
          && !existsUnitClauseOf(alit.var())) {
        if (var(alit).decision_level < DL)
          tmp_clause.push_back(alit);
        else
          lits_at_current_dl++;
        seen[alit.var()] = true;
      }
    }
  }
  if (!hasAntecedent(curr_lit)) {
    minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
  }
  if (var(curr_lit).decision_level > assertion_level_)
    assertion_level_ = var(curr_lit).decision_level;
}


void Solver::printOnlineStats() {
  if (config_.quiet)
    return;

  cout << endl;
  cout << "time elapsed: " << stopwatch_.getElapsedSeconds() << "s" << endl;
  cout << "conflict clauses (all / bin / unit) \t";
  cout << num_conflict_clauses();
  cout << "/" << statistics_.num_binary_conflict_clauses_ << "/"
      << unit_clauses_.size() << endl << endl;

  cout << "cache size " << component_analyzer_.cache().used_memory_MB() << "MB"
      << endl;
  cout << "components (stored / hits) \t\t"
      << statistics_.cached_component_count() << "/" << statistics_.cache_hits()
      << endl;
  cout << "avg. variable count (stored / hits) \t"
      << statistics_.getAvgComponentSize() << "/"
      << statistics_.getAvgCacheHitSize();
  cout << endl;
  cout << "cache miss rate " << statistics_.cache_miss_rate() * 100 << "%"
      << endl;
}



// Start Strategy Generation

void Solver::initializeBLIF(ofstream& out){
  trace_->initExistPinID(num_variables());
  out << ".model strategy";
  out << "\n.inputs";
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == RANDOM )  
  //     out << " r" << i;
  // }

  for(auto v : orderedVar_){
    if(var2Q_[v] == RANDOM)
      out << " r" << v ;
  }

  out << "\n.outputs";
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << " e" << i;
  // }

  for(auto v : orderedVar_){
    if(var2Q_[v] == EXISTENTIAL)
      out << " e" << v ;
  }

  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << "\n.names " << trace_->existName(i) << "\n0";
  // } 

  for(auto v : orderedVar_){
    if(var2Q_[v] == EXISTENTIAL)
      out << "\n.names " << trace_->existName(v) << "\n0";
  }
}

void Solver::finalizeBLIF(ofstream& out){
  for(auto v : orderedVar_){
    if(var2Q_[v] == EXISTENTIAL)
      out << "\n.names " << trace_->existName(v) << " e" << v << "\n1 1";
  }
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << "\n.names " << trace_->existName(i) << " e" << i << "\n1 1";
  // } 
}

void Solver::generateStrategy(const string& output_file){
  // 1. initialize blif file
  ofstream out(output_file);
  initializeBLIF(out);
  trace_->writeStrategyToFile(out);
  finalizeBLIF(out);
  out.close();
}

void Solver::generateDNNF(const string& output_file){
  // 1. initialize blif file
  trace_->initExistPinID(num_variables());
  ofstream out(output_file);
  trace_->writeDNNF(out);
  out.close();
}

void Solver::generateCertificate(const string& up, const string& low, const string & prob)
{
  ofstream out(up);
  trace_->writeCertificate(out, true);
  out.close();

  out.open(low);
  trace_->writeCertificate(out, false);
  out.close();

  out.open(prob);
  out<<statistics_.final_solution_prob()<<"\n";
  out.close();
}

