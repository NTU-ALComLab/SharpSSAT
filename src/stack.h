/*
 * stack.h
 *
 *  Created on: Aug 23, 2012
 *      Author: Marc Thurley
 */

#ifndef STACK_H_
#define STACK_H_

#include "basic_types.h"
#include <cassert>

#define MAX(A,B) (A > B) ? A : B
#define MIN(A,B) (A < B) ? A : B
class StackLevel {
  /// active Component, once initialized, it should not change
  const unsigned super_component_ = 0;
  // branch
  bool active_branch_ = false;

  // offset in the literal stack where to store set lits
  const unsigned literal_stack_ofs_ = 0;

  //  Solutioncount
  mpz_class branch_model_count_[2] = {0,0};
  double branch_sat_prob_[2] = {DBL_ZERO, DBL_ZERO};
  bool branch_found_unsat_[2] = {false,false};

  //NOTE ssat
  double  path_prob_[2] = {1.0, 1.0}; // set lits prob
  double  dec_prob_ = 0; // active_branch = 0
  bool    isR_ = true;
  bool    isU_ = false;
  bool    isInv_ = false;
  Node*   node_ = nullptr;

  /// remaining Components

  // the start offset in the component stack for
  // the remaining components in this decision level
  // all remaining components can hence be found in
  // [remaining_components_ofs_, "nextLevel".remaining_components_begin_)
  const unsigned remaining_components_ofs_ = 0;

  // boundary of the stack marking which components still need to be processed
  // all components to be processed can be found in
  // [remaining_components_ofs_, unprocessed_components_end_)
  // also, all processed, can be found
  // in [unprocessed_components_end_, component_stack.size())
  unsigned unprocessed_components_end_ = 0;
public:

  bool hasUnprocessedComponents() {
    assert(unprocessed_components_end_ >= remaining_components_ofs_);
    return unprocessed_components_end_ > remaining_components_ofs_;
  }
  void nextUnprocessedComponent() {
    assert(unprocessed_components_end_ > remaining_components_ofs_);
    unprocessed_components_end_--;
  }

  void resetRemainingComps() {
    unprocessed_components_end_ = remaining_components_ofs_;
  }
  unsigned super_component() {
    return super_component_;
  }
  unsigned remaining_components_ofs() {
    return remaining_components_ofs_;
  }
  void set_unprocessed_components_end(unsigned end) {
    unprocessed_components_end_ = end;
    assert(remaining_components_ofs_ <= unprocessed_components_end_);
  }

  StackLevel(unsigned super_comp, unsigned lit_stack_ofs,
      unsigned comp_stack_ofs) :
      super_component_(super_comp),
      literal_stack_ofs_(lit_stack_ofs),
      remaining_components_ofs_(comp_stack_ofs),
      unprocessed_components_end_(comp_stack_ofs) {
    assert(super_comp < comp_stack_ofs);
  }

  unsigned currentRemainingComponent() {
    assert(remaining_components_ofs_ <= unprocessed_components_end_ - 1);
    return unprocessed_components_end_ - 1;
  }

  bool isSecondBranch() {
    return active_branch_;
  }

  bool needSecondBranch(){
    //NOTE in ssat if current branch prob=1 and isExist, no need to second branch
    if(isR_) return true;
    if(isU_){
      if( active_branch_==0 && (branch_sat_prob_[0]*path_prob_[0])==double(0) ) return false;
      return true;
    }
    if( active_branch_==0 &&  (branch_sat_prob_[0]*path_prob_[0])==double(1) ) return false;    // on first exist branch, prob=1
    if( active_branch_==1 && ((branch_sat_prob_[0]*path_prob_[0]) >=
                              (branch_sat_prob_[1]*path_prob_[1])) ){                           // on second exist branch, existential early return
      return false;
    }
    return true;
  }

  void changeBranch() {
    active_branch_ = true;
  }

  bool anotherCompProcessible() {
    return (!branch_found_unsat()) && hasUnprocessedComponents();
  }

  unsigned literal_stack_ofs() {
    return literal_stack_ofs_;
  }

  void includeSolution(const mpz_class &solutions) {
    if (branch_found_unsat_[active_branch_]) {
      assert(branch_model_count_[active_branch_] == 0);
      return;
    }
    if (solutions == 0)
      branch_found_unsat_[active_branch_] = true;
    if (branch_model_count_[active_branch_] == 0)
      branch_model_count_[active_branch_] = solutions;
    else
      branch_model_count_[active_branch_] *= solutions;
  }

  void includeSolution(unsigned solutions) {
    if (branch_found_unsat_[active_branch_]) {
      assert(branch_model_count_[active_branch_] == 0);
      return;
    }
    if (solutions == 0)
      branch_found_unsat_[active_branch_] = true;
    if (branch_model_count_[active_branch_] == 0)
      branch_model_count_[active_branch_] = solutions;
    else
      branch_model_count_[active_branch_] *= solutions;

  }

  void includeSatProb(double prob) {
    //cout << super_component_ << " include prob=" << prob << endl;
    if (branch_found_unsat_[active_branch_]) {
      //assert(branch_model_count_[active_branch_] == 0);
      return;
    }
    if ( prob == DBL_ZERO){
      branch_found_unsat_[active_branch_] = true;
      branch_sat_prob_[active_branch_] = DBL_ZERO;
    }
    if (branch_sat_prob_[active_branch_] == DBL_ZERO)
      branch_sat_prob_[active_branch_] = prob;
    else
      branch_sat_prob_[active_branch_] *= prob;
  }

  void includePathProb(double prob){
    //cout << super_component_ << " include implied " << prob << " to "<< super_component_ << endl;
    path_prob_[active_branch_] *= prob;
  }


  bool branch_found_unsat() {
    return branch_found_unsat_[active_branch_];
  }
  void mark_branch_unsat() {
    branch_found_unsat_[active_branch_] = true;
  }

  const mpz_class getTotalModelCount() const {
    return branch_model_count_[0] + branch_model_count_[1];
  }

  void setIsDecRandom(bool r){
    isR_ = r;
  }

  void setIsDecUniver(bool r){
    isU_ = r;
  }

  void setDecProb(double p){
    dec_prob_ = p;
  }

  double getCurPathProb(){
    return path_prob_[active_branch_];
  }

  double getTotalSatProb() const{
    // cout << super_component_ << " branch prob=" << 
    //         path_prob_[0]*branch_sat_prob_[0] << ", " << path_prob_[1]*branch_sat_prob_[1] << endl;
    if(isU_) return MIN( path_prob_[0]*branch_sat_prob_[0], path_prob_[1]*branch_sat_prob_[1]);
    if(!isR_) return MAX( path_prob_[0]*branch_sat_prob_[0], path_prob_[1]*branch_sat_prob_[1]);
    return (dec_prob_*path_prob_[0]*branch_sat_prob_[0] + (1-dec_prob_)*path_prob_[1]*branch_sat_prob_[1]);
  }

  void setIsInv(bool inv){
    isInv_ = inv;
  }


  // decision variable v
  // 0 for v' side, 1 for v side 
  bool maxProbBranch(){
    assert(!isR_ && !isU_);
    bool b = path_prob_[0]*branch_sat_prob_[0] < path_prob_[1]*branch_sat_prob_[1];
    // cout << path_prob_[0]*branch_sat_prob_[0] << " " << path_prob_[1]*branch_sat_prob_[1] << endl;
    // cout << b << endl;
    return isInv_ ? (!b) : b;
  }

  bool minProbBranch(){
    assert(isU_);
    bool b = path_prob_[0]*branch_sat_prob_[0] >= path_prob_[1]*branch_sat_prob_[1];
    // cout << path_prob_[0]*branch_sat_prob_[0] << " " << path_prob_[1]*branch_sat_prob_[1] << endl;
    // cout << b << endl;
    return isInv_ ? (!b) : b;
  }

  void setNode(Node* n){
    node_ = n;
  }

  Node* getNode(){
    return node_;
  }

  // bool currentBranch(){
  //   return isInv_ ? ~active_branch_ : active_branch_;
  // }

};

class DecisionStack: public vector<StackLevel> {
  unsigned int failed_literal_test_active = 0;
public:

  //begin for implicit BCP
  void startFailedLitTest() {
    failed_literal_test_active = true;
  }
  void stopFailedLitTest() {
    failed_literal_test_active = false;
  }
  //end for implicit BCP

  StackLevel &top() {
    assert(size() > 0);
    return back();
  }
  int get_decision_level() const {
    assert(size() > 0);
    return size() - 1 + failed_literal_test_active;
  } // 0 means pre-1st-decision

};



#endif /* STACK_H_ */
