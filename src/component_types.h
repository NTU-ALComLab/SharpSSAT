/*
 * component_types.h
 *
 *  Created on: Aug 23, 2012
 *      Author: Marc Thurley
 */

#ifndef COMPONENT_TYPES_H_
#define COMPONENT_TYPES_H_

#include <assert.h>
#include <vector>
#include <math.h>

#include "basic_types.h"
#include "structures.h"
#include "containers.h"
#include "strategy.h"
using namespace std;

#define NIL_ENTRY 0

typedef unsigned CacheEntryID;
typedef unsigned ComponentDataType;

// State values for variables found during component
// analysis (CA)
typedef unsigned char CA_SearchState;
#define   CA_NIL  0
#define   CA_IN_SUP_COMP  1
#define   CA_SEEN 2
#define   CA_IN_OTHER_COMP  3

#define varsSENTINEL  0
#define clsSENTINEL   NOT_A_CLAUSE

template <class T>
 class BitStuffer {
 public:
  BitStuffer(T *data):data_start_(data),p(data){
    *p = 0;
  }

  void stuff(const unsigned val, const unsigned num_bits_val){
      assert(num_bits_val > 0);
      assert((val >> num_bits_val) == 0);
      if(end_of_bits_ == 0)
        *p = 0;
      assert((*p >> end_of_bits_) == 0);
      *p |= val << end_of_bits_;
      end_of_bits_ += num_bits_val;
      if (end_of_bits_ > _bits_per_block){
        //assert(*p);
        end_of_bits_ -= _bits_per_block;
        *(++p) = val >> (num_bits_val - end_of_bits_);
        assert(!(end_of_bits_ == 0) | (*p == 0));
      }
      else if (end_of_bits_ == _bits_per_block){
        end_of_bits_ -= _bits_per_block;
        p++;
      }
  }

  void assert_size(unsigned size){
    if(end_of_bits_ == 0)
       p--;
    assert(p - data_start_ == size - 1);
  }

 private:
  T *data_start_ = nullptr;
  T *p = nullptr;
  // in the current block
  // the bit postion just after the last bit written
  unsigned end_of_bits_ = 0;

  static const unsigned _bits_per_block = (sizeof(T) << 3);

};



//  the identifier of the components
class Component {
public:

  void reserveSpace(unsigned int num_variables, unsigned int num_clauses) {
    data_.reserve(num_variables + num_clauses + 2);
  }

  void set_id(CacheEntryID id) {
    id_ = id;
  }

  CacheEntryID id() {
    return id_;
  }

  void addVar(const VariableIndex var) {
    // the only time a varsSENTINEL is added should be in a
    // call to closeVariableData(..)
    assert(var != varsSENTINEL);
    data_.push_back(var);
  }

  void closeVariableData() {
    data_.push_back(varsSENTINEL);
    clauses_ofs_ = data_.size();
  }

  void addCl(const ClauseIndex cl) {
    // the only time a clsSENTINEL is added should be in a
    // call to closeClauseData(..)
    assert(cl != clsSENTINEL);
    data_.push_back(cl);
  }

  void closeClauseData() {
    data_.push_back(clsSENTINEL);
  }

  vector<VariableIndex>::const_iterator varsBegin() const {
    return data_.begin();
  }

  vector<ClauseIndex>::const_iterator clsBegin() const {
    return data_.begin() + clauses_ofs_;
  }

  unsigned num_variables() const {
    return clauses_ofs_ - 1;
  }

  unsigned numLongClauses() const {
    return data_.size() - clauses_ofs_ - 1;
  }

  bool empty() const {
    return data_.empty();
  }

  // ssat added v to remove inactive variable FIXME for model count
  // only called by the first component analysis
  void createAsDummyComponent(unsigned max_var_id, unsigned max_clause_id, LiteralIndexedVector<TriValue>& v) {
    data_.clear();
    clauses_ofs_ = 1;
    for (unsigned idvar = 1; idvar <= max_var_id; idvar++){
      if (v[ LiteralID(idvar, false) ]==X_TRI)
        addVar(idvar);
    }
    closeVariableData();
    if (max_clause_id > 0)
      for (unsigned idcl = 1; idcl <= max_clause_id; idcl++){
        //cout << "add cl " << idcl << endl;
        addCl(idcl);
      }
    closeClauseData();
  }

  void print(){
    cout << "Var={";
    int i=0;
    for(; i<num_variables(); ++i ){
      cout << data_[i];
      if (i!=num_variables()-1) cout << ',';
    }
    cout << "} Cls={";
    i = clauses_ofs_;
    for(;i<data_.size()-1; ++i){
      cout << data_[i];
      if (i!=data_.size()-2) cout << ',';
    }
    cout << "}" << endl;
  }


private:
  // data_ stores the component data:
  // for better cache performance the
  // clause and variable data are stored in
  // a contiguous piece of memory
  // variables SENTINEL clauses SENTINEL
  // this order has to be taken care of on filling
  // in the data!
  vector<unsigned> data_;
  unsigned clauses_ofs_ = 0;
  // id_ will identify denote the entry in the cacheable component database,
  // where a Packed version of this component is stored
  // yet this does not imply that the model count of this component is already known
  // once the model count is known, a link to the packed component will be stored
  // in the hash table
  CacheEntryID id_ = 0;

  // NOTE flag indicating if the component contains only exist var.

};

// Packed Component Base Class

class BasePackedComponent {
public:
  static unsigned bits_per_variable() {
    return _bits_per_variable;
  }
  static unsigned variable_mask() {
      return _variable_mask;
  }
  static unsigned bits_per_clause() {
    return _bits_per_clause;
  }

  static unsigned bits_per_block(){
	  return _bits_per_block;
  }

  static unsigned bits_of_data_size(){
    return _bits_of_data_size;
  }

  static void adjustPackSize(unsigned int maxVarId, unsigned int maxClId);

  BasePackedComponent() {}
  BasePackedComponent(unsigned creation_time): creation_time_(creation_time) {}

  ~BasePackedComponent() {
    if (data_)
      delete data_;
  }
  static void outbit(unsigned v){
   for(auto i=0; i<32;i++){
      cout << ((v&2147483648)?"1":"0");
      v&=2147483648-1;
      v <<= 1;
    }
  }

  static unsigned log2(unsigned v){
         // taken from
         // http://graphics.stanford.edu/~seander/bithacks.html#IntegerLogLookup
         static const char LogTable256[256] =
         {
         #define LT(n) n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n
             -1, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3,
             LT(4), LT(5), LT(5), LT(6), LT(6), LT(6), LT(6),
             LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7)
         };

         unsigned r;     // r will be lg(v)
         unsigned int t, tt; // temporaries

         if ((tt = (v >> 16)))
         {
           r = (t = (tt >> 8)) ? 24 + LogTable256[t] : 16 + LogTable256[tt];
         }
         else
         {
           r = (t = (v >> 8)) ? 8 + LogTable256[t] : LogTable256[v];
         }
         return r;
  }

  unsigned creation_time() {
    return creation_time_;
  }

  const mpz_class &model_count() const {
    return model_count_;
  }

  double sat_prob() const{
    return sat_prob_;
  }

  void set_node(Node* n){
    node_ = n;
  }

  Node* get_node(){
    return node_;
  }

  unsigned alloc_of_model_count() const{
        return sizeof(mpz_class)
               + model_count_.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
  }

  void set_creation_time(unsigned time) {
    creation_time_ = time;
  }

  void set_model_count(const mpz_class &rn, unsigned time) {
    model_count_ = rn;
    length_solution_period_and_flags_ = (time - creation_time_) | (length_solution_period_and_flags_ & 1);
  }

  void set_sat_prob(double prob, unsigned time){
    sat_prob_ = prob;
    length_solution_period_and_flags_ = (time - creation_time_) | (length_solution_period_and_flags_ & 1);
  }

  void set_sat_prob(double prob){
    sat_prob_ = prob;
    //length_solution_period_and_flags_ = (time - creation_time_) | (length_solution_period_and_flags_ & 1);
  }

  unsigned hashkey() const  {
    return hashkey_;
  }

  bool modelCountFound(){
    return (length_solution_period_and_flags_ >> 1);
  }

 // inline bool equals(const BasePackedComponent &comp) const;

  // a cache entry is deletable
  // only if it is not connected to an active
  // component in the component stack
  bool isDeletable() const {
    return length_solution_period_and_flags_ & 1;
  }
  void set_deletable() {
    length_solution_period_and_flags_ |= 1;
  }

  void clear() {
    // before deleting the contents of this component,
    // we should make sure that this component is not present in the component stack anymore!
    assert(isDeletable());
    if (data_)
      delete data_;
    data_ = nullptr;
  }

  static unsigned _debug_static_val;

protected:
  // data_ contains in packed form the variable indices
  // and clause indices of the component ordered
  // structure is
  // var var ... clause clause ...
  // clauses begin at clauses_ofs_
  unsigned* data_ = nullptr;

  unsigned hashkey_ = 0;

  mpz_class model_count_;
  double    sat_prob_;
  Node*     node_;
  

  unsigned creation_time_ = 1;


  // this is:  length_solution_period = length_solution_period_and_flags_ >> 1
  // length_solution_period == 0 means unsolved
  // and the first bit is "delete_permitted"
  unsigned length_solution_period_and_flags_ = 0;

  // deletion is permitted only after
  // the copy of this component in the stack
  // does not exist anymore


protected:
  static unsigned _bits_per_clause, _bits_per_variable; // bitsperentry
  static unsigned _bits_of_data_size; // number of bits needed to store the data size
  static unsigned _data_size_mask;
  static unsigned _variable_mask, _clause_mask;
  static const unsigned _bits_per_block= (sizeof(unsigned) << 3);

};










class DiffPackedComponent {
public:
  static unsigned bits_per_variable() {
    return _bits_per_variable;
  }
  static unsigned bits_per_clause() {
    return _bits_per_clause;
  }

  static void adjustPackSize(unsigned int maxVarId, unsigned int maxClId);

  DiffPackedComponent() {
  }

  DiffPackedComponent(Component &rComp) {
    unsigned max_diff = 0;

    for (auto it = rComp.varsBegin() + 1; *it != varsSENTINEL; it++) {
      if (*it - *(it - 1) > max_diff)
        max_diff = *it - *(it - 1);
    }

    unsigned bits_per_var_diff = (unsigned int) ceil(
        log((double) max_diff + 1) / log(2.0));

    max_diff = 0;
    for (auto jt = rComp.clsBegin() + 1; *jt != clsSENTINEL; jt++) {
      if (*jt - *(jt - 1) > max_diff)
        max_diff = *jt - *(jt - 1);
    }

    unsigned bits_per_clause_diff = (unsigned int) ceil(
        log((double) max_diff + 1) / log(2.0));


    unsigned data_size = (_bits_per_variable + 5 + _bits_per_clause + 5
        + (rComp.num_variables() - 1) * bits_per_var_diff
        + (rComp.numLongClauses() - 1) * bits_per_clause_diff) / _bitsPerBlock
        + 3;

    unsigned * p = data_ = (unsigned*) malloc(sizeof(unsigned) * data_size);

    *p = bits_per_var_diff;
    unsigned int bitpos = 5;

    *p |= *rComp.varsBegin() << bitpos;
    bitpos += _bits_per_variable;
    unsigned hashkey_vars = *rComp.varsBegin();

    for (auto it = rComp.varsBegin() + 1; *it != varsSENTINEL; it++) {
      *p |= ((*it) - *(it - 1)) << bitpos;
      bitpos += bits_per_var_diff;
      hashkey_vars = hashkey_vars * 3 + ((*it) - *(it - 1));
      if (bitpos >= _bitsPerBlock) {
        bitpos -= _bitsPerBlock;
        *(++p) = (((*it) - *(it - 1)) >> (bits_per_var_diff - bitpos));
      }
    }
    if (bitpos > 0)
      p++;
    clauses_ofs_ = p - data_;

    unsigned hashkey_clauses = *rComp.clsBegin();
    if (*rComp.clsBegin()) {
      *p = bits_per_clause_diff;
      bitpos = 5;
      *p |= *rComp.clsBegin() << bitpos;
      bitpos += _bits_per_clause;
      for (auto jt = rComp.clsBegin() + 1; *jt != clsSENTINEL; jt++) {
        *p |= ((*jt - *(jt - 1)) << (bitpos));
        bitpos += bits_per_clause_diff;
        hashkey_clauses = hashkey_clauses * 3 + (*jt - *(jt - 1));
        if (bitpos >= _bitsPerBlock) {
          bitpos -= _bitsPerBlock;
          *(++p) = ((*jt - *(jt - 1)) >> (bits_per_clause_diff - bitpos));
        }
      }
      if (bitpos > 0)
        p++;
    }
    *p = 0;
    hashkey_ = hashkey_vars + (((unsigned long) hashkey_clauses) << 16);
  }

  DiffPackedComponent(Component &rComp, const mpz_class &model_count,
      unsigned long time) :
      DiffPackedComponent(rComp) {
    model_count_ = model_count;
    creation_time_ = time;
  }

  ~DiffPackedComponent() {
    if (data_)
      delete data_;
  }

  unsigned data_size() const {
    if (!data_)
      return 0;
    unsigned *p = data_;
    while (*p)
      p++;
    return (p - data_ + 1);
  }

  unsigned creation_time() {
    return creation_time_;
  }

  const mpz_class &model_count() const {
    return model_count_;
  }

  double sat_prob() const { return sat_prob_;}

  void set_creation_time(unsigned time) {
    creation_time_ = time;
  }

  void set_model_count(const mpz_class &rn) {
    model_count_ = rn;
  }

  void set_sat_prob(double prob){ sat_prob_ = prob;}

  unsigned hashkey() {
    return hashkey_;
  }

  // NOTE that the following is only an upper bound on
  // the number of varaibles
  // it might overcount by a few variables
  // this is due to the way things are packed
  // and to reduce time needed to compute this value
  unsigned num_variables() {
    unsigned bits_per_var_diff = (*data_) & 31;
    return 1 + (clauses_ofs_ * sizeof(unsigned) * 8 - _bits_per_variable - 5) / bits_per_var_diff;
  }
//  unsigned num_variables() {
//      return (clauses_ofs_ * sizeof(unsigned) * 8) /_bits_per_variable;
//  }

  bool equals(const DiffPackedComponent &comp) const {
    if (clauses_ofs_ != comp.clauses_ofs_)
      return false;
    unsigned* p = data_;
    unsigned* r = comp.data_;
    while (*p && *p == *r) {
      p++;
      r++;
    }
    return *p == *r;
  }

protected:
  // data_ contains in packed form the variable indices
  // and clause indices of the component ordered
  // structure is
  // var var ... clause clause ...
  // clauses begin at clauses_ofs_
  unsigned* data_ = nullptr;
  unsigned clauses_ofs_ = 0;
  unsigned hashkey_ = 0;

  mpz_class model_count_;
  double sat_prob_;
  unsigned creation_time_ = 0;

private:
  static unsigned _bits_per_clause, _bits_per_variable; // bitsperentry
  static unsigned _variable_mask, _clause_mask;
  static const unsigned _bitsPerBlock = (sizeof(unsigned) << 3);

};

class SimpleUnpackedComponent : public BasePackedComponent {
public:

  SimpleUnpackedComponent() {
  }

  SimpleUnpackedComponent(Component &rComp) {
    unsigned data_size = rComp.num_variables() +  rComp.numLongClauses() + 2;

    unsigned *p = data_ =  new unsigned[data_size];

    *p = data_size;
    *(++p) = rComp.num_variables();
    unsigned hashkey_vars = 0;
    for (auto it = rComp.varsBegin(); *it != varsSENTINEL; it++) {
      *(++p) = *it;
      hashkey_vars = (hashkey_vars *3) + *it;
    }

    unsigned hashkey_clauses = 0;

    for (auto jt = rComp.clsBegin(); *jt != clsSENTINEL; jt++) {
        *(++p) = *jt;
        hashkey_clauses = (hashkey_clauses *3) + *jt;
    }
    //*(++p) = 0;
    hashkey_ = hashkey_vars + (((unsigned) hashkey_clauses) << 16);

    assert(p - data_ + 1 == data_size);

  }

  unsigned num_variables() {
      return *(data_+1);
  }

  unsigned data_size() const {
    if (!data_) return 0;
    return *data_;
  }

  unsigned data_only_byte_size() const {
    return data_size()* sizeof(unsigned);
  }

  unsigned raw_data_byte_size() const {
    return data_size()* sizeof(unsigned)
          + model_count_.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
  }

  bool equals(const SimpleUnpackedComponent &comp) const {
    if(hashkey_ != comp.hashkey())
      return false;
    unsigned* p = data_;
    unsigned* r = comp.data_;
    while(p != data_ + data_size()) {
        if(*(p++) != *(r++))
            return false;
    }
    return true;
  }
};

class DifferencePackedComponent:public BasePackedComponent {
public:

  DifferencePackedComponent() {
  }

  DifferencePackedComponent(Component &rComp) {

    unsigned max_var_diff = 0;
    unsigned hashkey_vars = *rComp.varsBegin();
    for (auto it = rComp.varsBegin() + 1; *it != varsSENTINEL; it++) {
      hashkey_vars = (hashkey_vars * 3) + *it;
      if ((*it - *(it - 1)) - 1 > max_var_diff)
        max_var_diff = (*it - *(it - 1)) - 1 ;
    }

    unsigned hashkey_clauses = *rComp.clsBegin();
    unsigned max_clause_diff = 0;
    if (*rComp.clsBegin()) {
      for (auto jt = rComp.clsBegin() + 1; *jt != clsSENTINEL; jt++) {
        hashkey_clauses = hashkey_clauses*3 + *jt;
        if (*jt - *(jt - 1) - 1 > max_clause_diff)
          max_clause_diff = *jt - *(jt - 1) - 1;
      }
    }

    hashkey_ = hashkey_vars + ((unsigned) hashkey_clauses << 11) + ((unsigned) hashkey_clauses >> 23);

    //VERIFIED the definition of bits_per_var_diff and bits_per_clause_diff
    unsigned bits_per_var_diff = log2(max_var_diff) + 1;
    unsigned bits_per_clause_diff = log2(max_clause_diff) + 1;

    assert(bits_per_var_diff <= 31);
    assert(bits_per_clause_diff <= 31);

    unsigned data_size_vars = bits_of_data_size() + 2*bits_per_variable() + 5;

    data_size_vars += (rComp.num_variables() - 1) * bits_per_var_diff ;

    unsigned data_size_clauses = 0;
    if(*rComp.clsBegin())
      data_size_clauses += bits_per_clause() + 5
        + (rComp.numLongClauses() - 1) * bits_per_clause_diff;

    unsigned data_size = (data_size_vars + data_size_clauses)/bits_per_block();
      data_size+=  ((data_size_vars + data_size_clauses) % bits_per_block())? 1 : 0;

    data_ = new unsigned[data_size];

    assert((data_size >> bits_of_data_size()) == 0);
    BitStuffer<unsigned> bs(data_);

    bs.stuff(data_size, bits_of_data_size());
    bs.stuff(rComp.num_variables(), bits_per_variable());
    bs.stuff(bits_per_var_diff, 5);
    bs.stuff(*rComp.varsBegin(), bits_per_variable());

    if(bits_per_var_diff)
    for (auto it = rComp.varsBegin() + 1; *it != varsSENTINEL; it++)
      bs.stuff(*it - *(it - 1) - 1, bits_per_var_diff);


    if (*rComp.clsBegin()) {
      bs.stuff(bits_per_clause_diff, 5);
      bs.stuff(*rComp.clsBegin(), bits_per_clause());
      if(bits_per_clause_diff)
      for (auto jt = rComp.clsBegin() + 1; *jt != clsSENTINEL; jt++)
        bs.stuff(*jt - *(jt - 1) - 1, bits_per_clause_diff);
    }

    // to check wheter the "END" block of bits_per_clause()
    // many zeros fits into the current
    //bs.end_check(bits_per_clause());
    // this will tell us if we computed the data_size
    // correctly
    bs.assert_size(data_size);
  }

  unsigned num_variables() const{
    uint64_t *p = (uint64_t *) data_;
    return (*p >> bits_of_data_size()) & (uint64_t) variable_mask();

  }

  unsigned data_size() const {
    if (!data_) return 0;
    return *data_ & _data_size_mask;
  }

  unsigned data_only_byte_size() const {
    return data_size()* sizeof(unsigned);
  }

  unsigned raw_data_byte_size() const {
    return data_size()* sizeof(unsigned)
      + model_count_.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
  }

    // raw data size with the overhead
    // for the supposed 16byte alignment of malloc
//     unsigned sys_overhead_raw_data_byte_size() const {
//       unsigned ds = data_size()* sizeof(unsigned);
//       unsigned ms = model_count_.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
// //      unsigned mask = 0xfffffff8;
// //      return (ds & mask) + ((ds & 7)?8:0)
// //            +(ms & mask) + ((ms & 7)?8:0);
//       unsigned mask = 0xfffffff0;
//             return (ds & mask) + ((ds & 15)?16:0)
//                   +(ms & mask) + ((ms & 15)?16:0);
//     }

  bool equals(const DifferencePackedComponent &comp) const {
    if(hashkey_ != comp.hashkey())
      return false;
    unsigned* p = data_;
    unsigned* r = comp.data_;
    while(p != data_ + data_size()) {
        if(*(p++) != *(r++))
            return false;
    }
    return true;
  }

private:

};

class SimplePackedComponent : public BasePackedComponent {
public:

  SimplePackedComponent() {
  }

  SimplePackedComponent(Component &rComp) {
    unsigned data_size_vars = bits_of_data_size() + bits_per_variable() + rComp.num_variables() * bits_per_variable();
    unsigned data_size_clauses = rComp.numLongClauses() * bits_per_clause();
    unsigned data_size = (data_size_vars + data_size_clauses)/bits_per_block();

    data_size+=  ((data_size_vars + data_size_clauses) % bits_per_block())? 1 : 0;

    data_ =  new unsigned[data_size];

    BitStuffer<unsigned> bs(data_);
    unsigned hashkey_vars = 0;
    unsigned hashkey_clauses = 0;

    assert((data_size >> bits_of_data_size()) == 0);

    bs.stuff(data_size, bits_of_data_size());
    bs.stuff(rComp.num_variables(),bits_per_variable());

    for (auto it = rComp.varsBegin(); *it != varsSENTINEL; it++) {
      hashkey_vars = (hashkey_vars *3) + *it;
      bs.stuff(*it, bits_per_variable());
    }

    if (*rComp.clsBegin())
      for (auto jt = rComp.clsBegin(); *jt != clsSENTINEL; jt++) {
        hashkey_clauses = (hashkey_clauses *3) + *jt;
        bs.stuff(*jt, bits_per_clause());
      }
    bs.assert_size(data_size);

    hashkey_ = hashkey_vars + (((unsigned) hashkey_clauses) << 16);
  }

  unsigned num_variables() const{
    uint64_t *p = (uint64_t *) data_;
    return (*p >> bits_of_data_size()) & (uint64_t) variable_mask();
  }

  unsigned data_size() const {
    if (!data_) return 0;
    return *data_ & _data_size_mask;
  }

  unsigned data_only_byte_size() const {
      return data_size()* sizeof(unsigned);
  }

  unsigned raw_data_byte_size() const {
        return data_size()* sizeof(unsigned)
             + model_count_.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
  }

  bool equals(const SimplePackedComponent &comp) const {
    if(hashkey_ != comp.hashkey())
      return false;
    unsigned* p = data_;
    unsigned* r = comp.data_;
    while(p != data_ + data_size()) {
        if(*(p++) != *(r++))
            return false;
    }
    return true;
  }

};




//typedef DiffPackedComponent PackedComponent;
 typedef DifferencePackedComponent PackedComponent;
// typedef SimpleUnpackedComponent PackedComponent;
//  typedef SimplePackedComponent PackedComponent;


// CachedComponent Adds Structure to PackedComponent that is
// necessary to store it in the cache
// namely, the descendant tree structure that
// allows for the removal of cache pollutions
class CachedComponent: public PackedComponent {

  // the position where this
  // component is stored in the component stack
  // if this is non-zero, we may not simply delete this
  // component
  unsigned component_stack_id_ = 0;

  // theFather and theDescendants:
  // each CCacheEntry is a Node in a tree which represents the relationship
  // of the components stored
  CacheEntryID father_ = 0;
  CacheEntryID first_descendant_ = 0;
  CacheEntryID next_sibling_ = 0;

public:
  // a cache entry is deletable
  // only if it is not connected to an active
  // component in the component stack
  bool deletable() {
    return component_stack_id_ == 0;
  }
  void eraseComponentStackID() {
    component_stack_id_ = 0;
  }
  void setComponentStackID(unsigned id) {
    component_stack_id_ = id;
  }
  unsigned component_stack_id() {
    return component_stack_id_;
  }

  void setNode(Node* n){
    set_node(n);
  }

  void clear() {
    // before deleting the contents of this component,
    // we should make sure that this component is not present in the component stack anymore!
    assert(component_stack_id_ == 0);
    if (data_)
      delete data_;
    data_ = nullptr;
  }

  CachedComponent() {
  }

  // CachedComponent(Component &comp, const mpz_class &model_count,
  //     unsigned long time) :
  //     PackedComponent(comp, model_count, time) {
  // }

  CachedComponent(Component &comp) :
      PackedComponent(comp) {
  }
  unsigned long SizeInBytes() const {
    return sizeof(CachedComponent)
        + PackedComponent::data_size() * sizeof(unsigned)
        // and add the memory usage of model_count_
        // which is:
        + sizeof(mpz_class)
        + model_count().get_mpz_t()->_mp_size * sizeof(mp_limb_t);
  }

  // BEGIN Cache Pollution Management

  void set_father(CacheEntryID f) {
    father_ = f;
  }
  const CacheEntryID father() const {
    return father_;
  }

  void set_next_sibling(CacheEntryID sibling) {
    next_sibling_ = sibling;
  }
  CacheEntryID next_sibling() {
    return next_sibling_;
  }

  void set_first_descendant(CacheEntryID descendant) {
    first_descendant_ = descendant;
  }
  CacheEntryID first_descendant() {
    return first_descendant_;
  }
};

class CacheBucket: protected vector<CacheEntryID> {
  friend class ComponentCache;

public:

  using vector<CacheEntryID>::size;

  unsigned long getBytesMemoryUsage() {
    return sizeof(CacheBucket) + size() * sizeof(CacheEntryID);
  }
};


//#include "component_types-inl.h"

#endif /* COMPONENT_TYPES_H_ */
