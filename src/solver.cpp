/*
 * solver.cpp
 *
 *  Created on: Aug 23, 2012
 *      Author: marc
 */
#include "solver.h"
#include <cstdint>
#include <deque>

// extern string TmpInstance(int a, int b, int c, string tmp_dir) ;
// extern TreeDecomposition TreeDecompose(const Graph& graph, double time, string tmp_dir);

template <typename TProb>
void Solver<TProb>::print(vector<LiteralID> &vec) {
  for (auto l : vec)
    cout << l.toInt() << " ";
  cout << endl;
}

template <typename TProb>
void Solver<TProb>::print(vector<unsigned> &vec) {
  for (auto l : vec)
    cout << l << " ";
  cout << endl;
}

template <typename TProb>
bool Solver<TProb>::simplePreProcess() {
  if (!config_.perform_pre_processing)
    return true;
  assert(literal_stack_.size() == 0);
  unsigned start_ofs = 0;
//BEGIN process unit clauses
  for (auto lit : this->unit_clauses_){
    if(this->qType(lit)==UNIVERSAL){
      if(config_.strategy_generation){
        univ_imp_.push_back(lit.neg().toInt());
        initTrace();
        stack_.back().getNode()->recordUnivImplications(univ_imp_);
      }
      return false;
    }
    setLiteralIfFree(lit);
    if(this->literal_values_[lit] != T_TRI){
        return false;
    }
    stack_.top().includePathProb( this->prob(lit) );
    if(this->qType(lit)==EXISTENTIAL)
      exist_imp_.push_back(lit.toInt());
    else{
        assert(this->qType(lit) == RANDOM);
        random_imp_.push_back(lit.toInt());
    }
  }
//END process unit clauses
  if (config_.include_forall) {
    if (containUniversalClause()) return false;
  }
  bool succeeded = BCP(start_ofs);

  if (succeeded && !config_.ssat_solving)
    succeeded &= prepFailedLiteralTest();

  if (succeeded){
    if (config_.ssat_solving){
      //FIXME
      const TProb& assert_prob_ = stack_.top().getCurPathProb();
      LiteralIndexedVector<TriValue> lv = LiteralIndexedVector<TriValue>(this->literal_values_);
      HardWireAndCompact();
      this->literal_values_ = lv;
      stack_.top().includePathProb(assert_prob_);
      if (config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        stack_.top().getNode()->recordExistImplications(exist_imp_);
        stack_.top().getNode()->recordRandomImplications(random_imp_);
      }
    }
    else
      HardWireAndCompact();
  }else{
    if (config_.ssat_solving && config_.strategy_generation && config_.include_forall)
      stack_.top().getNode()->recordUnivImplications(univ_imp_);
  }
  return succeeded;
}

template <typename TProb>
bool Solver<TProb>::containUniversalClause() {
  // Check bin clauses
  for (LiteralID l(1, false); l != this->literals_.end_lit(); l.inc()) {
    if (this->qType(l) != UNIVERSAL) continue;
    //BEGIN Propagate Bin Clauses
    for (auto bt = this->literal(l).binary_links_.begin(); *bt != SENTINEL_LIT; bt++) {
      if (this->qType(*bt) == UNIVERSAL) {
        if (!config_.quiet)
          cout << "Found universal bin clause!" << endl;
        if (config_.strategy_generation) {
          univ_imp_.push_back(l.neg().toInt());
          univ_imp_.push_back(bt->neg().toInt());
          initTrace();
          stack_.back().getNode()->recordUnivImplications(univ_imp_);
        }
        return true;
      }
    }
  }

  // Check long clauses
  bool all_universal = false;
  for (auto it_lit = this->literal_pool_.begin(); it_lit != this->literal_pool_.end(); it_lit++) {
    if (*it_lit == SENTINEL_LIT) {
      if (all_universal) {
        if (!config_.quiet)
          cout << "Found universal long clause!" << endl;
        --it_lit;
        if (config_.strategy_generation) {
          for ( ; *it_lit != SENTINEL_LIT; --it_lit) {
            univ_imp_.push_back(it_lit->neg().toInt());
          }
          initTrace();
          stack_.back().getNode()->recordUnivImplications(univ_imp_);
        }
        return true;
      }
      all_universal = true;
      if (it_lit + 1 == this->literal_pool_.end())
        break;
      it_lit += ClauseHeader::overheadInLits();
    } else {
      if (this->qType(*it_lit) != UNIVERSAL) all_universal = false;
    }
  }
  if (!config_.quiet)
    cout << "No universal clauses found in preprocessing" << endl;
  return false;
}

template <typename TProb>
bool Solver<TProb>::prepFailedLiteralTest() {
  unsigned last_size;
  do {
    last_size = literal_stack_.size();
    for (unsigned v = 1; v < this->variables_.size(); v++)
      if (this->isActive(v)) {
        unsigned sz = literal_stack_.size();
        setLiteralIfFree(LiteralID(v, true));
        bool res = BCP(sz);
        while (literal_stack_.size() > sz) {
          this->unSet(literal_stack_.back());
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
            this->unSet(literal_stack_.back());
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

template <typename TProb>
void Solver<TProb>::HardWireAndCompact() {
  this->compactClauses();
  if(!config_.ssat_solving)
    this->compactVariables();
  else{
    this->unit_clauses_.clear();
  }
  literal_stack_.clear();

  for (auto l = LiteralID(1, false); l != this->literals_.end_lit(); l.inc()) {
    this->literal(l).activity_score_ = this->literal(l).binary_links_.size() - 1;
    this->literal(l).activity_score_ += this->occurrence_lists_[l].size();
  }


  this->statistics_.num_unit_clauses_ = this->unit_clauses_.size();

  this->statistics_.num_original_binary_clauses_ = this->statistics_.num_binary_clauses_;
  this->statistics_.num_original_unit_clauses_ = this->statistics_.num_unit_clauses_ =
      this->unit_clauses_.size();
  initStack(this->num_variables());
  if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation)
    initTrace();
  this->original_lit_pool_size_ = this->literal_pool_.size();
}

template <typename TProb>
bool Solver<TProb>::solve(const string &file_name) {
  stopwatch_.start();
  this->statistics_.input_file_ = file_name;

  if (!this->createfromFile(file_name)) return false;
  initStack(this->num_variables());
  if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation)
    initTrace();

  if (!config_.quiet) {
    cout << "Solving " << file_name << endl;
    this->statistics_.printShortFormulaInfo();
  }
  if (!config_.quiet)
    cout << endl << "Preprocessing .." << flush;

  // SSAT must have preprocessing
  bool notfoundUNSAT = simplePreProcess();
  if (!config_.quiet)
    cout << " DONE" << endl;

  if (notfoundUNSAT) {
	  if(this->num_variables() == 0){
        // TODO: Check whether this is affected by HardWireAndCompact
		  this->statistics_.exit_state_ = SUCCESS;
		  this->statistics_.set_final_solution_count(1.0);
          if(config_.compile_DNNF || config_.certificate_generation){
            stack_.top().getNode()->addDescendant(trace_->getConstant(1));
          }
  }else{

    if (!config_.quiet) {
      this->statistics_.printShortFormulaInfo();
    }

    last_ccl_deletion_time_ = last_ccl_cleanup_time_ = this->statistics_.getTime();

    state_.violated_clause.reserve(this->num_variables());
    component_analyzer_.initialize(this->literals_, this->literal_pool_, this->var2Q_);


    this->statistics_.exit_state_ = config_.ssat_solving ? countSSAT() : countSAT();

    if(config_.ssat_solving){
      this->statistics_.set_final_solution_prob(assert_prob_*stack_.top().getTotalSatProb());
    }
    else{
      this->statistics_.set_final_solution_count(stack_.top().getTotalModelCount());
    }
    this->statistics_.num_long_conflict_clauses_ = this->num_conflict_clauses();
    this->statistics_.cache_bytes_memory_usage_ =
        component_analyzer_.cache().recompute_bytes_memory_usage();
	  }
  } else {
    this->statistics_.exit_state_ = SUCCESS;
    this->statistics_.set_final_solution_count(0.0);
    cout << endl << " FOUND UNSAT DURING PREPROCESSING " << endl;

    if(config_.compile_DNNF || config_.certificate_generation){
        stack_.top().getNode()->addDescendant(trace_->getConstant(0));
    }
  }
  cout << "End of Solving" << endl;
  if(config_.strategy_generation){
    cout << "Start Generating Strategy..." << endl;
    Node::resetGlobalVisited();
    this->statistics_.set_num_nodes(trace_->numNodes());
    this->statistics_.set_num_edges(trace_->numEdges());
  }
  else if(config_.compile_DNNF){
    cout << "Start Generating DNNF..." << endl;
    Node::resetGlobalVisited();
    this->statistics_.set_num_nodes(trace_->numNodes());
    this->statistics_.set_num_edges(trace_->numEdges());
    // TODO: change DNNF name
    generateDNNF(config_.DNNF_filename);
  }
  else if(config_.certificate_generation){
    cout << "Start Generating Certificate..." << endl;
    Node::resetGlobalVisited();
    this->statistics_.set_num_nodes(trace_->numNodes());
    this->statistics_.set_num_edges(trace_->numEdges());
  }
  stopwatch_.stop();
  this->statistics_.time_elapsed_ = stopwatch_.getElapsedSeconds();
  this->statistics_.writeToFile("data.out");
  if(!SolverConfiguration::quiet)
    this->statistics_.printShort();

  return true;
}

template <typename TProb>
SOLVER_StateT Solver<TProb>::countSAT() {
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
template <typename TProb>
SOLVER_StateT Solver<TProb>::countSSAT() {
  retStateT res = RESOLVED;

  while (true) {
    //NOTE assertion failed
    //assert(state_.name != STATE_ASSERTION_PENDING);
    while (component_analyzer_.findNextRemainingComponentOf(stack_.top())) {
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation)
        setPureLiteralsOnTrace();
      ssatDecideLiteral();
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

template <typename TProb>
void Solver<TProb>::decideLiteral() {
  // establish another decision stack level
  stack_.push_back(
      StackLevel<TProb>(stack_.top().currentRemainingComponent(),
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
      this->literal(LiteralID(max_score_var, true)).activity_score_
          > this->literal(LiteralID(max_score_var, false)).activity_score_);
  setLiteralIfFree(theLit);
  setState(STATE_ASSERTION_PENDING);
  this->statistics_.num_decisions_++;

  if (this->statistics_.num_decisions_ % 128 == 0)
    this->decayActivities();

  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());
}

template <typename TProb>
bool Solver<TProb>::ssatDecideLiteral() {
  // establish another decision stack level
  // cout << "New Stack " << stack_.size() << ", Comp " << stack_.top().currentRemainingComponent() << endl;
  stack_.push_back(
      StackLevel<TProb>(stack_.top().currentRemainingComponent(),
          literal_stack_.size(), component_analyzer_.component_stack_size()));


  float max_score = -1;
  float score;
  unsigned max_score_var = 0;
  int max_score_lev = this->statistics_.num_qlev + 1;
  for (auto it = component_analyzer_.superComponentOf(stack_.top()).varsBegin();
      *it != varsSENTINEL; it++) {
    this->variables_[*it].component_level++;
    assert(this->variables_[*it].component_level == stack_.get_decision_level());
    if (!this->isActive(LiteralID(*it, false))) continue;
    score = scoreOf(*it);
    if( this->qlev(*it) < max_score_lev ){
      max_score = score;
      max_score_var = *it;
      max_score_lev = this->qlev(*it);
    }
    else if ( (score > max_score) && (this->qlev(*it) == max_score_lev) ) {
      max_score = score;
      max_score_var = *it;
      max_score_lev = this->qlev(*it);
    }
  }

  // this assert should always hold,
  // if not then there is a bug in the logic of countSAT();
  assert(max_score_var != 0);

  LiteralID theLit(max_score_var,
      this->literal(LiteralID(max_score_var, true)).activity_score_
          > this->literal(LiteralID(max_score_var, false)).activity_score_);

  setLiteralIfFree(theLit);

  setState(STATE_ASSERTION_PENDING);
  this->statistics_.num_decisions_++;

  if (this->statistics_.num_decisions_ % 128 == 0)
    this->decayActivities();

  //ssat NOTE
  stack_.top().setIsDecRandom( this->qType(theLit)==RANDOM );
  stack_.top().setIsDecUniver( this->qType(theLit)==UNIVERSAL );
  stack_.top().setDecProb( this->prob(theLit) );
  stack_.top().setIsInv( theLit.sign() );
  if (config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation) {
    Node* n  = new Node();
    n->setDecVar(theLit.var(), this->qType(theLit)==RANDOM, this->qType(theLit)==UNIVERSAL, theLit.sign());
    stack_.top().setNode(n);
  }
  // cout << "Decide " << theLit.toInt() << endl;
  // cout << "Node count: " << trace_->numNodes() << endl;
  // cout << "Decision level: " << stack_.get_decision_level() << endl;

  return true;
  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());
}

template <typename TProb>
retStateT Solver<TProb>::backtrack() {
  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());
  do {
    if (stack_.top().branch_found_unsat()){
      component_analyzer_.removeAllCachePollutionsOf(stack_.top());
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        if(!config_.include_forall){
          // only remove descendents if universal strategies aren't needed
          Node* n = stack_.top().getNode();
          assert(n);
          n->removeAllDescendants(n->getCurrentBranch());
          n->addDescendant(trace_->getConstant(0));
        }
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
    if (config_.ssat_solving) {
      for (auto it = component_analyzer_.superComponentOf(stack_.top()).varsBegin();
          *it != varsSENTINEL; it++) {
        this->variables_[*it].component_level--;
      }

      TProb p = stack_.top().getTotalSatProb();
      if (config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation) {
        Node* n = stack_.top().getNode();
        assert(n);
        if (n->isExist()) {
          // cout << "Mark Max Branch " << stack_.top().maxProbBranch() << endl;
          n->markMaxBranch(stack_.top().maxProbBranch());
        } else if (n->isUniv()) {
          n->markMinBranch(stack_.top().minProbBranch());
        }
        component_analyzer_.cacheSatProbOf(stack_.top().super_component(), p, n);
      }
      else component_analyzer_.cacheSatProbOf(stack_.top().super_component(), p, nullptr);

      if (stack_.get_decision_level() <= 0)
        break;
      reactivateTOS();

      assert(stack_.size() >= 2);
      (stack_.end()-2)->includeSatProb(p);
      if (config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation) {
        assert((stack_.end()-2)->getNode());
        assert(stack_.top().getNode());
        ((stack_.end()-2)->getNode())->addDescendant(stack_.top().getNode());
      }
    }
    else {
      mpz_class model_count = stack_.top().getTotalModelCount();
      component_analyzer_.cacheModelCountOf(stack_.top().super_component(), model_count);

      if (stack_.get_decision_level() <= 0)
        break;
      reactivateTOS();

      assert(stack_.size() >= 2);
      (stack_.end() - 2)->includeSolution(model_count);
    }
    stack_.pop_back();
    // step to the next component not yet processed
    stack_.top().nextUnprocessedComponent();

    assert(
        stack_.top().remaining_components_ofs() < component_analyzer_.component_stack_size()+1);

  } while (stack_.get_decision_level() >= 0);
  return EXIT;
}

template <typename TProb>
retStateT Solver<TProb>::resolveConflict() {
  this->statistics_.num_conflicts_++;

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
    this->var(TOS_decLit().neg()).ante = this->addUIPConflictClause(uip_clauses_.back());
    ant = this->var(TOS_decLit()).ante;
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
  if (config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation)
    stack_.top().getNode()->changeBranch();
  LiteralID lit = TOS_decLit();
  reactivateTOS();
  setLiteralIfFree(lit.neg(), ant);
  setState(STATE_ASSERTION_PENDING);
  // END Backtracking
  return RESOLVED;
}

template <typename TProb>
bool Solver<TProb>::bcp() {
  assert(
      stack_.top().remaining_components_ofs() <= component_analyzer_.component_stack_size());
  assert(state_.name == STATE_ASSERTION_PENDING);
// the asserted literal has been set, so we start
// bcp on that literal
  unsigned start_ofs = literal_stack_.size() - 1;

  if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
    exist_imp_.clear();
    random_imp_.clear();
    if(config_.include_forall)
      univ_imp_.clear();
  }

//BEGIN process unit clauses
  for (auto lit : this->unit_clauses_){
    // NOTE we may possibly assign a unit literal as decLit
    //      that falsifies the formula
    if (this->var(lit).component_level != stack_.get_decision_level()) continue;
    if(setLiteralIfFree(lit)){
      //cout << "assign unit clause" << endl;
      stack_.top().includePathProb( this->prob(lit) );
      if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
        if(this->qType(lit)==EXISTENTIAL)
          exist_imp_.push_back(lit.toInt());
        else if(this->qType(lit)==UNIVERSAL){
          univ_imp_.push_back(lit.neg().toInt());
          // Node* n = stack_.top().getNode();
          // n->addDescendant(trace_->getConstant(0));
          // cout << "find universal unit clause" << endl;
          // return false;
        }
        else{
            assert(this->qType(lit) == RANDOM);
            random_imp_.push_back(lit.toInt());
        }
      }
    }
    else{
      //cout << "unit clause already assigned" << endl;
      if(this->literal_values_[lit]==F_TRI)
        cout << "Warning!! already unsat" << endl;
    }
  }
//END process unit clauses

  setState(STATE_NIL);
  bool bSucceeded = BCP(start_ofs);

  // if (config_.perform_failed_lit_test && bSucceeded) {
  //   bSucceeded = implicitBCP();
  // }
  

  if (!bSucceeded) {
    assert(state_.name == STATE_CONFLICT);
    recordLastUIPCauses();

    if (this->statistics_.num_clauses_learned_ - last_ccl_deletion_time_
        > this->statistics_.clause_deletion_interval()) {
      this->deleteConflictClauses();
      last_ccl_deletion_time_ = this->statistics_.num_clauses_learned_;
    }

    if (this->statistics_.num_clauses_learned_ - last_ccl_cleanup_time_ > 100000) {
      this->compactConflictLiteralPool();
      last_ccl_cleanup_time_ = this->statistics_.num_clauses_learned_;
    }
  }

  if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
    Node* n = stack_.top().getNode();
    if(bSucceeded){
      n->recordExistImplications(exist_imp_);
      n->recordRandomImplications(random_imp_);
    }
    else{
        n->addDescendant(trace_->getConstant(0));
        if(config_.include_forall){
          n->recordUnivImplications(univ_imp_);
        }
    }
  }

  return bSucceeded;
}

//TODO include path prob into stack_.top
template <typename TProb>
bool Solver<TProb>::BCP(unsigned start_at_stack_ofs) {
  for (unsigned int i = start_at_stack_ofs; i < literal_stack_.size(); i++) {
    LiteralID unLit = literal_stack_[i].neg();
    //BEGIN Propagate Bin Clauses
    for (auto bt = this->literal(unLit).binary_links_.begin(); *bt != SENTINEL_LIT;
        bt++) {
      if (this->var(*bt).component_level != stack_.get_decision_level()) continue;
      if (this->isResolved(*bt)) {
        setConflictState(unLit, *bt);
        return false;
      }
      if (this->isActive(*bt) && this->qType(*bt) == UNIVERSAL) {
        if (config_.strategy_generation)
          univ_imp_.push_back(bt->neg().toInt());
        setConflictState(unLit, *bt);
        return false;
      }
      if(setLiteralIfFree(*bt, Antecedent(unLit))){
        stack_.top().includePathProb( this->prob(*bt) );
        if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
          if(this->qType(*bt)==EXISTENTIAL){
            exist_imp_.push_back( (*bt).toInt() );
          }
          else{
            assert(this->qType(*bt) == RANDOM);
            random_imp_.push_back( (*bt).toInt() );
          }
        };
      }
    }
    //END Propagate Bin Clauses

    for (auto itcl = this->literal(unLit).watch_list_.rbegin(); *itcl != SENTINEL_CL;
        itcl++) {
      bool isLitA = (*this->beginOf(*itcl) == unLit);
      auto p_watchLit = this->beginOf(*itcl) + 1 - isLitA;
      auto p_otherLit = this->beginOf(*itcl) + isLitA;

      if (this->var(*p_otherLit).component_level != stack_.get_decision_level()) continue;
      if (this->isSatisfied(*p_otherLit))
        continue;
      auto itL = this->beginOf(*itcl) + 2;
      while (this->isResolved(*itL))
        itL++;
      // either we found a free or satisfied lit
      if (*itL != SENTINEL_LIT) {
        this->literal(*itL).addWatchLinkTo(*itcl);
        swap(*itL, *p_watchLit);
        *itcl = this->literal(unLit).watch_list_.back();
        this->literal(unLit).watch_list_.pop_back();
      } else {
        // or p_unLit stays resolved
        // and we have hence no free literal left
        // for p_otherLit remain poss: Active or Resolved
        if (this->isActive(*p_otherLit) && this->qType(*p_otherLit) == UNIVERSAL) { // active universal otherLit
          if (config_.strategy_generation)
            univ_imp_.push_back(p_otherLit->neg().toInt());
          setConflictState(*itcl);
          return false;
        }
        if (setLiteralIfFree(*p_otherLit, Antecedent(*itcl))) { // implication
          stack_.top().includePathProb( this->prob(*p_otherLit) );
          if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
            if(this->qType(*p_otherLit)==EXISTENTIAL){
              exist_imp_.push_back( (*p_otherLit).toInt() );
            }
            else{
                assert(this->qType(*p_otherLit) == RANDOM);
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

/* template <typename TProb>
bool Solver<TProb>::implicitBCP() {
  static vector<LiteralID> test_lits(this->num_variables());
  static LiteralIndexedVector<unsigned char> viewed_lits(this->num_variables() + 1,
      0);

  unsigned stack_ofs = stack_.top().literal_stack_ofs();
  while (stack_ofs < literal_stack_.size()) {
    test_lits.clear();
    for (auto it = literal_stack_.begin() + stack_ofs;
        it != literal_stack_.end(); it++) {
      for (auto cl_ofs : this->occurrence_lists_[it->neg()])
        if (!this->isSatisfied(cl_ofs)) {
          for (auto lt = this->beginOf(cl_ofs); *lt != SENTINEL_LIT; lt++)
            if (this->isActive(*lt) && !viewed_lits[lt->neg()]) {
              test_lits.push_back(lt->neg());
              viewed_lits[lt->neg()] = true;

            }
        }
    }

    stack_ofs = literal_stack_.size();
    for (auto jt = test_lits.begin(); jt != test_lits.end(); jt++)
      viewed_lits[*jt] = false;

    for (auto lit : test_lits)
      if (this->isActive(lit)) {
        unsigned sz = literal_stack_.size();
        // we increase the decLev artificially
        // s.t. after the tentative BCP call, we can learn a conflict clause
        // relative to the assignment of *jt
        stack_.startFailedLitTest();
        setLiteralIfFree(lit);

        assert(!this->hasAntecedent(lit));

        bool bSucceeded = BCP(sz);
        if (!bSucceeded)
          recordAllUIPCauses();

        stack_.stopFailedLitTest();

        while (literal_stack_.size() > sz) {
          this->unSet(literal_stack_.back());
          literal_stack_.pop_back();
        }

        if (!bSucceeded) {
          sz = literal_stack_.size();
          for (auto it = uip_clauses_.rbegin(); it != uip_clauses_.rend();
              it++) {
            setLiteralIfFree(it->front(), this->addUIPConflictClause(*it));
          }
          if (!BCP(sz))
            return false;
        }
      }
  }
  return true;
} */

///////////////////////////////////////////////////////////////////////////////////////////////
// BEGIN module conflictAnalyzer
///////////////////////////////////////////////////////////////////////////////////////////////

template <typename TProb>
void Solver<TProb>::minimizeAndStoreUIPClause(LiteralID uipLit,
    vector<LiteralID> & tmp_clause, uint8_t seen[]) {
  static deque<LiteralID> clause;
  clause.clear();
  assertion_level_ = -1;
  for (auto lit : tmp_clause) {
    if (this->existsUnitClauseOf(lit.var()))
      continue;
    bool resolve_out = false;
    if (this->hasAntecedent(lit)) {
      resolve_out = true;
      if (this->getAntecedent(lit).isAClause()) {
        for (auto it = this->beginOf(this->getAntecedent(lit).asCl()) + 1;
            *it != SENTINEL_CL; it++)
          if ((seen[it->var()] ^ it->sign()) != 2) {
            resolve_out = false;
            break;
          }
      } else {
        LiteralID alit = this->getAntecedent(lit).asLit();
        if ((seen[alit.var()] ^ alit.sign()) != 2) {
          resolve_out = false;
        }
      }
    }

    if (!resolve_out) {
      // uipLit should be the sole literal of this Decision Level
      if (this->var(lit).decision_level >= assertion_level_) {
        assertion_level_ = this->var(lit).decision_level;
        clause.push_front(lit);
      } else
        clause.push_back(lit);
    }
  }

  if (uipLit.var() != 0) {
    assert(this->var(uipLit).decision_level== stack_.get_decision_level());
    clause.push_front(uipLit);
  }
  uip_clauses_.push_back(vector<LiteralID>(clause.begin(), clause.end()));
}

template <typename TProb>
void Solver<TProb>::recordLastUIPCauses() {
// note:
// variables of lower dl: if seen we dont work with them anymore
// variables of this dl: if seen we incorporate their
// antecedent and set to unseen
  assert(state_.name == STATE_CONFLICT);

  uint8_t seen[this->num_variables() + 1]; // bit 0: phase; bit 1: included
  memset(seen, 0, sizeof(uint8_t) * (this->num_variables() + 1));

  static vector<LiteralID> tmp_clause;
  tmp_clause.clear();

  assertion_level_ = -1;
  uip_clauses_.clear();

  unsigned lit_stack_ofs = literal_stack_.size();
  int DL = stack_.get_decision_level();
  unsigned lits_at_current_dl = 0;

  for (auto l : state_.violated_clause) {
    if (this->var(l).decision_level == 0 || this->existsUnitClauseOf(l.var()))
      continue;
    if (this->var(l).decision_level < DL)
      tmp_clause.push_back(l);
    else
      lits_at_current_dl++;
    this->literal(l).increaseActivity();
    seen[l.var()] = 2 ^ l.sign();
  }

  LiteralID curr_lit;
  while (lits_at_current_dl) {
    assert(lit_stack_ofs != 0);
    curr_lit = literal_stack_[--lit_stack_ofs];

    if (!seen[curr_lit.var()])
      continue;

    seen[curr_lit.var()] = 0;

    // if (lits_at_current_dl == 1) {
      // perform UIP stuff
      if (TOS_decLit() == curr_lit) {
        // this should be the decision literal when in first branch
        // or it is a literal decided to explore in failed literal testing
        //assert(stack_.TOS_decLit() == curr_lit);
        break;
      }
    // }
    lits_at_current_dl--;

    assert(this->hasAntecedent(curr_lit));

    if (this->getAntecedent(curr_lit).isAClause()) {
      this->updateActivities(this->getAntecedent(curr_lit).asCl());
      assert(curr_lit == *this->beginOf(this->getAntecedent(curr_lit).asCl()));

      if (config_.include_forall) {
        bool resolved = true;
        for (auto it = this->beginOf(this->getAntecedent(curr_lit).asCl()) + 1; *it != SENTINEL_CL; it++) {
          if ((seen[it->var()] ^ it->sign()) == 3) {
            resolved = false;
            break;
          }
        }
        if (!resolved) {
          tmp_clause.push_back(curr_lit.neg());
          continue;
        }
      }

      for (auto it = this->beginOf(this->getAntecedent(curr_lit).asCl()) + 1;
          *it != SENTINEL_CL; it++) {
        if (seen[it->var()] || this->var(*it).decision_level == 0
            || this->existsUnitClauseOf(it->var()))
          continue;
        if (this->var(*it).decision_level < DL)
          tmp_clause.push_back(*it);
        else
          lits_at_current_dl++;
        seen[it->var()] = 2 ^ it->sign();
      }
    } else {
      LiteralID alit = this->getAntecedent(curr_lit).asLit();
      this->literal(alit).increaseActivity();
      this->literal(curr_lit).increaseActivity();

      if (config_.include_forall) {
        if ((seen[alit.var()] ^ alit.sign()) == 3) {
          tmp_clause.push_back(curr_lit.neg());
          continue;
        }
      }

      if (!seen[alit.var()] && this->var(alit).decision_level != 0
          && !this->existsUnitClauseOf(alit.var())) {
        if (this->var(alit).decision_level < DL)
          tmp_clause.push_back(alit);
        else
          lits_at_current_dl++;
        seen[alit.var()] = 2 ^ alit.sign();
      }
    }
    curr_lit = NOT_A_LIT;
  }

  minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);

  if (this->var(curr_lit).decision_level > assertion_level_)
    assertion_level_ = this->var(curr_lit).decision_level;
}

/* template <typename TProb>
void Solver<TProb>::recordAllUIPCauses() {
// note:
// variables of lower dl: if seen we dont work with them anymore
// variables of this dl: if seen we incorporate their
// antecedent and set to unseen

  assert(state_.name == STATE_CONFLICT);

  bool seen[this->num_variables() + 1];
  memset(seen, false, sizeof(bool) * (this->num_variables() + 1));

  static vector<LiteralID> tmp_clause;
  tmp_clause.clear();

  assertion_level_ = -1;
  uip_clauses_.clear();

  unsigned lit_stack_ofs = literal_stack_.size();
  int DL = stack_.get_decision_level();
  unsigned lits_at_current_dl = 0;

  for (auto l : state_.violated_clause) {
    if (this->var(l).decision_level == 0 || this->existsUnitClauseOf(l.var()))
      continue;
    if (this->var(l).decision_level < DL)
      tmp_clause.push_back(l);
    else
      lits_at_current_dl++;
    this->literal(l).increaseActivity();
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
      if (!this->hasAntecedent(curr_lit)) {
        // this should be the decision literal when in first branch
        // or it is a literal decided to explore in failed literal testing
        //assert(stack_.TOS_decLit() == curr_lit);
        break;
      }
      // perform UIP stuff
      minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
    }

    assert(this->hasAntecedent(curr_lit));

    if (this->getAntecedent(curr_lit).isAClause()) {
      this->updateActivities(this->getAntecedent(curr_lit).asCl());
      assert(curr_lit == *this->beginOf(this->getAntecedent(curr_lit).asCl()));

      for (auto it = this->beginOf(this->getAntecedent(curr_lit).asCl()) + 1;
          *it != SENTINEL_CL; it++) {
        if (seen[it->var()] || this->var(*it).decision_level == 0
            || this->existsUnitClauseOf(it->var()))
          continue;
        if (this->var(*it).decision_level < DL)
          tmp_clause.push_back(*it);
        else
          lits_at_current_dl++;
        seen[it->var()] = true;
      }
    } else {
      LiteralID alit = this->getAntecedent(curr_lit).asLit();
      this->literal(alit).increaseActivity();
      this->literal(curr_lit).increaseActivity();
      if (!seen[alit.var()] && this->var(alit).decision_level != 0
          && !this->existsUnitClauseOf(alit.var())) {
        if (this->var(alit).decision_level < DL)
          tmp_clause.push_back(alit);
        else
          lits_at_current_dl++;
        seen[alit.var()] = true;
      }
    }
  }
  if (!this->hasAntecedent(curr_lit)) {
    minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
  }
  if (this->var(curr_lit).decision_level > assertion_level_)
    assertion_level_ = this->var(curr_lit).decision_level;
} */

template <typename TProb>
void Solver<TProb>::printOnlineStats() {
  if (config_.quiet)
    return;

  cout << endl;
  cout << "time elapsed: " << stopwatch_.getElapsedSeconds() << "s" << endl;
  cout << "conflict clauses (all / bin / unit) \t";
  cout << this->num_conflict_clauses();
  cout << "/" << this->statistics_.num_binary_conflict_clauses_ << "/"
      << this->unit_clauses_.size() << endl << endl;

  cout << "cache size " << component_analyzer_.cache().used_memory_MB() << "MB"
      << endl;
  cout << "components (stored / hits) \t\t"
      << this->statistics_.cached_component_count() << "/" << this->statistics_.cache_hits()
      << endl;
  cout << "avg. variable count (stored / hits) \t"
      << this->statistics_.getAvgComponentSize() << "/"
      << this->statistics_.getAvgCacheHitSize();
  cout << endl;
  cout << "cache miss rate " << this->statistics_.cache_miss_rate() * 100 << "%"
      << endl;
}



// Start Strategy Generation

template <typename TProb>
void Solver<TProb>::initializeBLIF(ofstream& out){
  trace_->initExistPinID(this->num_variables());
  out << ".model strategy";
  out << "\n.inputs";
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == RANDOM )  
  //     out << " r" << i;
  // }

  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == RANDOM)
      out << " r" << v ;
  }

  out << "\n.outputs";
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << " e" << i;
  // }

  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == EXISTENTIAL)
      out << " e" << v ;
  }

  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << "\n.names " << trace_->existName(i) << "\n0";
  // } 

  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == EXISTENTIAL)
      out << "\n.names " << trace_->existName(v) << "\n0";
  }
}

template <typename TProb>
void Solver<TProb>::finalizeBLIF(ofstream& out){
  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == EXISTENTIAL)
      out << "\n.names " << trace_->existName(v) << " e" << v << "\n1 1";
  }
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << "\n.names " << trace_->existName(i) << " e" << i << "\n1 1";
  // } 
}

template <typename TProb>
void Solver<TProb>::generateStrategy(const string& output_file){
  // 1. initialize blif file
  ofstream out(output_file);
  initializeBLIF(out);
  trace_->writeStrategyToFile(out);
  finalizeBLIF(out);
  out.close();
}

template <typename TProb>
void Solver<TProb>::generateDNNF(const string& output_file){
  // 1. initialize blif file
  trace_->initExistPinID(this->num_variables());
  ofstream out(output_file);
  trace_->writeDNNF(out);
  out.close();
}

template <typename TProb>
void Solver<TProb>::generateCertificate(const string& up, const string& low, const string & prob)
{
  ofstream out(up);
  trace_->writeCertificate(out, true);
  out.close();

  out.open(low);
  trace_->writeCertificate(out, false);
  out.close();

  out.open(prob);
  out<<this->statistics_.final_solution_prob()<<"\n";
  out.close();
}

template <typename TProb>
void Solver<TProb>::initializeExistBLIF(ofstream& out){
  trace_->initExistPinID(this->num_variables());
  out << ".model strategy";
  out << "\n.inputs";
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == RANDOM )  
  //     out << " r" << i;
  // }

  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == RANDOM)
      out << " r" << v ;
    else if(this->var2Q_[v] == UNIVERSAL)
      out << " a" << v ;
  }

  out << "\n.outputs";
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << " e" << i;
  // }

  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == EXISTENTIAL)
      out << " e" << v ;
  }

  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << "\n.names " << trace_->existName(i) << "\n0";
  // } 

  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == EXISTENTIAL)
      out << "\n.names " << trace_->existName(v) << "\n0";
  }
}

template <typename TProb>
void Solver<TProb>::initializeUnivBLIF(ofstream& out){
  trace_->initExistPinID(this->num_variables());
  out << ".model strategy";
  out << "\n.inputs";
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == RANDOM )  
  //     out << " r" << i;
  // }

  for(auto v : this->orderedVar_){
    // cout<<v<<" "<<var2Q_[v];
    if(this->var2Q_[v] == RANDOM)
      out << " r" << v ;
    else if(this->var2Q_[v] == EXISTENTIAL)
      out << " e" << v ;
  }

  out << "\n.outputs";
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << " e" << i;
  // }

  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == UNIVERSAL)
      out << " a" << v ;
  }

  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << "\n.names " << trace_->existName(i) << "\n0";
  // } 

  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == UNIVERSAL)
      out << "\n.names " << trace_->univName(v) << "\n0";
  }
}

template <typename TProb>
void Solver<TProb>::finalizeExistBLIF(ofstream& out){
  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == EXISTENTIAL)
      out << "\n.names " << trace_->existName(v) << " e" << v << "\n1 1";
  }
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << "\n.names " << trace_->existName(i) << " e" << i << "\n1 1";
  // } 
}

template <typename TProb>
void Solver<TProb>::finalizeUnivBLIF(ofstream& out){
  for(auto v : this->orderedVar_){
    if(this->var2Q_[v] == UNIVERSAL)
      out << "\n.names " << trace_->univName(v) << " a" << v << "\n1 1";
  }
  // for(size_t i=1; i<=num_variables(); ++i){
  //   if(var2Lev_[i]==-1) continue; // unused variables;
  //   if(var2Q_[i] == EXISTENTIAL )  
  //     out << "\n.names " << trace_->existName(i) << " e" << i << "\n1 1";
  // } 
}

template <typename TProb>
void Solver<TProb>::generateExistStrategy(const string& output_file){
  // 1. initialize blif file
  ofstream out(output_file);
  initializeExistBLIF(out);
  trace_->writeExistStrategyToFile(out);
  // cout << "End treversing trace" << endl;
  finalizeExistBLIF(out);
  out.close();
}

template <typename TProb>
void Solver<TProb>::generateUnivStrategy(const string& output_file){
  // 1. initialize blif file
  ofstream out(output_file);
  initializeUnivBLIF(out);
  trace_->writeUnivStrategyToFile(out);
  // cout << "End treversing trace" << endl;
  finalizeUnivBLIF(out);
  out.close();
}

template class Solver<double>;
template class Solver<mpq_class>;
