#ifndef STRATEGY_H_
#define STRATEGY_H_

#include "structures.h"
#include <vector>
#include <cassert>
#include <fstream>
#include <sstream>

using namespace std;
// the trace of SSAT solving is represented as a DAG
// 2 kinds of node,  Random-Decision Node and Exist-Decision Node.

enum NodeType{
    RAND = 0,
    EXIST = 1,
    UNIV = 2,
    DUMMY = 3
};


class Node;     
class Trace; 


// for Decision Node on decision variable v, 
// descendants_[0] is v' and descendants_[1] is v.
class Node{
public:
    Node(NodeType t=DUMMY): refCnt_(0), type_(t), decVar_(0), curBranch_(0), prunedBranch_(0), visited_(0){
        Node::nodeCnt_++;
    }

    ~Node(){ Node::nodeCnt_--; }

    void setDecVar(unsigned v, bool isR, bool isU, bool sign){ 
        decVar_ = v; 
        //type_ = isR ? RAND : EXIST;
        if(isR){
            type_ = RAND;
        }else if(isU){
            type_ = UNIV;
        }else{
            type_ = EXIST;
        }
        curBranch_ = sign ? 1 : 0;
        // cout << "set current branch to " << curBranch_ << endl;
    }

    void markMaxBranch(bool b){ 
        assert(type_==EXIST);
        // cout << "Mark MaxBranch for " << decVar_ << " " << b << endl; 
        b_ = b; 
    }
    void markMinBranch(bool b){ 
        assert(type_==UNIV);
        // cout << "Mark MaxBranch for " << decVar_ << " " << b << endl; 
        b_ = b; 
    }
    void changeBranch(){ curBranch_ = !curBranch_; }
    bool getCurrentBranch(){ return curBranch_; }
    bool getPrunedBranch() { return prunedBranch_; }

    // branch 0 for v', branch 1 for v
    void addDescendant(Node* d){ 
        assert(d);
        assert(d!=this);
        assert( noDuplicateDescendants(d) );
        descendants_[curBranch_].push_back(d); 
        d->increaseRefCnt();
        Node::edgeCnt_ ++;
    }

    unsigned getRefCnt() { return refCnt_; }

    void removeAllDescendants(bool branch);

    // delete the branch of Exist node 
    // such that leaves max_branch only;
    void removeSmallBranch();

    bool isExist(){ return type_==EXIST ;}
    bool isUniv(){ return type_==UNIV ;}

    // debug function
    void printDescendants();

    void recordExistImplications(vector<int>& imp){
        existImp_[curBranch_] = imp;
    }

    void addExistImplication(int imp){
        existImp_[curBranch_].push_back(imp);
    }

    void recordRandomImplications(vector<int>& imp){
        randomImp_[curBranch_] = imp;
    }

    void addRandomImplication(int imp){
        randomImp_[curBranch_].push_back(imp);
    }

    void recordUnivImplications(vector<int>& imp){
        univImp_[curBranch_] = imp;
    }

    void addUnivImplication(int imp){
        univImp_[curBranch_].push_back(imp);
    }

    void recordPureLiterals(vector<int>& plit){
        pureLits_[curBranch_] = plit;
    }

    void addPureLiteral(int plit){
        pureLits_[curBranch_].push_back(plit);
    }

    vector<int>& getPureLiterals(){
        return pureLits_[curBranch_];
    }

    void setHasEarlyReturn(){ hasEarlyReturn_ = true; }
    void setPrunedBranch(bool b) { prunedBranch_ = b; }

    static void resetGlobalVisited(){ Node::globalVisited_++;}

    bool empty( bool isCertGen=false ) const{
        if (isCertGen)
            return descendants_[curBranch_].empty();
        return existImp_[curBranch_].empty() & randomImp_[curBranch_].empty() & descendants_[curBranch_].empty();
    }

    friend Trace;
    int             DNNFId = -1;    // DNNF node id

private: 
    void increaseRefCnt(){ ++refCnt_; }
    void decreaseRefCnt(){ assert(refCnt_!=0); --refCnt_; }
    void setDNNFId( int id ){ 
        assert( !visited() );
        assert( id >0 );
        DNNFId =  id;
        setVisited();
    }
    unsigned int getDNNFId(){ 
        assert( visited() );
        assert( DNNFId >0 );
        return DNNFId;
    }

    unsigned        refCnt_;        // number of in-coming edge
    vector<Node*>   descendants_[2];    
    NodeType        type_;
    unsigned        decVar_;        // decision variable
    bool            b_;             // maximum probability branch,
    bool            curBranch_; 
    vector<int>     existImp_[2];   // existential implications 
    vector<int>     univImp_[2];   // universal implications 
    vector<int>     randomImp_[2];  // random implications 
    vector<int>     pureLits_[2];   // pure literals
    bool            hasEarlyReturn_ = false;
    bool            prunedBranch_;


    // debug data member;
    size_t          visited_;

    // debug function
    bool noDuplicateDescendants(Node* n);
    bool visited(){ return visited_==globalVisited_;}
    void setVisited(){ visited_ = globalVisited_;}



    static unsigned nodeCnt_;
    static unsigned edgeCnt_;
    static size_t   globalVisited_;
};

// the trace is a DAG of single source
class Trace{
public:
    Trace(Node* s, Node* zero, Node* one): source_(s),constants_{zero,one}{ constants_[0]->increaseRefCnt(); constants_[1]->increaseRefCnt();};

    Trace(): source_(nullptr) {};

    ~Trace(){
        if(source_){
            source_->removeAllDescendants(1);
            delete source_;
        }
        if(constants_[0]){
            delete constants_[0];
        }
        if(constants_[1]){
            delete constants_[1];
        }
    };

    void print(){
        source_->printDescendants();
    }

    unsigned numNodes(){
        return Node::nodeCnt_;
    }

    unsigned numEdges(){
        return Node::edgeCnt_;
    }

    void cleanMinBranch(Node* n);
    string existName(size_t var){ return "e" + to_string(var) + "_" + to_string(existID[var]); }
    string univName(size_t var){ return "u" + to_string(var) + "_" + to_string(existID[var]); }
    size_t getExistID(size_t var){ return existID[var]; }
    void initExistPinID(size_t nVars){ existID.resize(nVars+1, 0); }

    void writeStrategyToFile(ofstream&);
    void writeExistStrategyToFile(ofstream&);
    void writeUnivStrategyToFile(ofstream&);
    void restoreRefCnt();
    void writeDNNF(ofstream&);
    void writeDNNFRecur(Node*);
    void writeCertificate(ofstream& out, bool isUp);
    void writeCertificateRecur(ofstream& out, Node *node, bool isUp);

    Node* getConstant(bool phase){ return constants_[phase]; }

private:
    Node*           source_;
    Node*           constants_[2];
    vector<size_t>  existID;
    size_t          intermediateID = 0;
    stringstream    ss;
    unsigned        nNode_ = 0;
    unsigned        nEdge_ = 0;
    vector<int>     lit2NodeId_;

    void    updateExist(size_t ev, size_t w, ofstream& out);
    void    updateUniv(size_t ev, size_t w, ofstream& out);
    void    updateIntermediate(size_t wire, vector<size_t>& par_wire, ofstream& out);
    size_t  updateRandom(size_t rv, size_t wire, bool sign, ofstream& out);
    size_t  updateUnivInput(size_t rv, size_t wire, bool sign, ofstream& out);
    size_t  updateExistInput(size_t rv, size_t wire, bool sign, ofstream& out);
};



#endif
