#ifndef STRATEGY_H_
#define STRATEGY_H_

#include "structures.h"
#include <vector>
#include <cassert>
#include <fstream>

using namespace std;
// the trace of SSAT solving is represented as a DAG
// 2 kinds of node,  Random-Decision Node and Exist-Decision Node.

enum NodeType{
    RAND = 0,
    EXIST = 1,
    DUMMY = 2
};


class Node;     
class Trace; 


// for Decision Node on decision variable v, 
// descendants_[0] is v' and descendants_[1] is v.
class Node{
public:
    Node(NodeType t=DUMMY): type_(t), refCnt_(0), decVar_(0), curBranch_(0), visited_(0){
        Node::nodeCnt_++;
    };

    ~Node(){ Node::nodeCnt_--; }

    void setDecVar(unsigned v, bool isR, bool sign){ 
        decVar_ = v; 
        type_ = isR ? RAND : EXIST;
        curBranch_ = sign ? 1 : 0;
        // cout << "set current branch to " << curBranch_ << endl;
    }

    void markMaxBranch(bool b){ 
        assert(type_==EXIST);
        // cout << "Mark MaxBranch for " << decVar_ << " " << b << endl; 
        b_ = b; 
    }
    void changeBranch(){ curBranch_ = !curBranch_; }
    bool getCurrentBranch(){ return curBranch_; };

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

    // debug function
    void printDescendants();

    void recordExistImplications(vector<int>& imp){
        existImp_[curBranch_] = imp;
    }

    void addExistImplication(int imp){
        existImp_[curBranch_].push_back(imp);
    }

    static void resetGlobalVisited(){ Node::globalVisited_++;}

    friend Trace;
private: 
    void increaseRefCnt(){ ++refCnt_; }
    void decreaseRefCnt(){ assert(refCnt_!=0); --refCnt_; }

    unsigned        refCnt_;        // number of in-coming edge
    vector<Node*>   descendants_[2];    
    NodeType        type_;
    unsigned        decVar_;        // decision variable
    bool            b_;             // maximum probability branch,
    bool            curBranch_; 
    //TODO also store existential implications here
    vector<int>     existImp_[2];   // existential implications 


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
    Trace(Node* s): source_(s), intermediateID(0){};

    Trace(): source_(NULL) {};

    ~Trace(){
        if(source_){
            source_->removeAllDescendants(1);
            delete source_;
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
    size_t getExistID(size_t var){ return existID[var]; }
    void initExistPinID(size_t nVars){ existID.resize(nVars+1, 0); }

    void writeStrategyToFile(ofstream&);

private:
    Node*           source_;
    vector<size_t>  existID;
    size_t          intermediateID;

    void    updateExist(size_t ev, size_t w, ofstream& out);
    void    updateIntermediate(size_t wire, vector<size_t>& par_wire, ofstream& out);
    size_t  updateRandom(size_t rv, size_t wire, bool sign, ofstream& out);
};



#endif