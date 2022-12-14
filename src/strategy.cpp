
#include "strategy.h"
#include <queue>
#include <unordered_map>

#define MAX_FILE_SIZE 1*long(1024)*long(1024*1024)

unsigned Node::nodeCnt_ = 0;
unsigned Node::edgeCnt_ = 0;
size_t   Node::globalVisited_ = 0;

typedef pair<size_t, vector<size_t>> WireInfo;  // its wire and parents wire;


bool Node::noDuplicateDescendants(Node* n){
    vector<Node*>& d = descendants_[curBranch_];
    for(size_t i=0; i<d.size(); ++i)
        if(n==d[i]) return false;
    return true;
}

void Node::removeAllDescendants(bool branch){
    vector<Node*>& d = descendants_[branch];
    for(size_t i=0; i<d.size(); ++i){
        assert(d[i]);
        d[i]->decreaseRefCnt();
        if(d[i]->getRefCnt()==0){
            d[i]->removeAllDescendants(0);
            d[i]->removeAllDescendants(1);
            delete d[i];
        }
        edgeCnt_ --;
    }
    vector<Node*>().swap(d);
    assert(descendants_[branch].empty());
}

// delete the branch of Exist node 
// such that leaves max_branch only;
void Node::removeSmallBranch(){
    if(visited()) return;
    if(type_==RAND){
        for(size_t i=0; i<2; ++i){
            for(size_t j=0; j<descendants_[i].size(); ++j){
                descendants_[i][j]->removeSmallBranch();
            }
        }
    }
    else if(type_==EXIST){
        removeAllDescendants( !b_ );
        for(size_t i=0; i<descendants_[b_].size(); ++i){
            Node* d = descendants_[b_][i];
            descendants_[b_][i]->removeSmallBranch();
        }

    }
    else{ // DUMMY
        for(size_t i=0; i<descendants_[1].size(); ++i)
            descendants_[1][i]->removeSmallBranch();
    }
    setVisited();
}

// debug 
void Node::printDescendants(){
    if(visited()) return;
    if(type_==EXIST){
        cout << this << "\tMaxBr=" << decVar_ << (b_ ? "" : "'" ) << endl;
    }
    if(!descendants_[0].empty()){
        cout << this << "\t[L " << decVar_ << "]" << endl;
        for(size_t i=0; i<descendants_[0].size(); ++i){
            assert(descendants_[0][i]);
            cout << "Edge " << this << " -> " << descendants_[0][i] << endl;
            descendants_[0][i]->printDescendants();
        }
    }

    if(!descendants_[1].empty()){
        cout << this << "\t[R " << decVar_ << "]" << endl;
        for(size_t i=0; i<descendants_[1].size(); ++i){
            assert(descendants_[1][i]);
            cout << "Edge " << this << " -> " << descendants_[1][i] << endl;
            descendants_[1][i]->printDescendants();
        }
    }
    setVisited();
}

void Trace::updateExist(size_t ev, size_t w, ofstream& out){
    out << "\n.names" << " w" << w << " " << existName(ev);
    existID[ev]++;
    out << " " << existName(ev) << "\n00 0"; // e' = e v w
}

void Trace::updateIntermediate(size_t wire, vector<size_t>& par_wire, ofstream& out){
    // out << "\n# update intermetiate";
    out << "\n.names";
    for(size_t i=0; i<par_wire.size(); ++i)
        out << " w" << par_wire[i];
    out << " w" << wire;
    out << "\n" << string(par_wire.size(), '0') << " 0";
}

// new_wire = wire & (rv' or rv)
size_t Trace::updateRandom(size_t rv, size_t wire, bool sign, ofstream& out){
    size_t new_wire = intermediateID + (sign ? 1 : 2);
    out << "\n.names";
    out << " w" << wire << " r" << rv << " w" << new_wire;
    out << "\n1" << ( sign ? "0" : "1") << " 1";
    return new_wire;
}

void Trace::writeStrategyToFile(ofstream& out){
    // compact DAG, remove samll branch of exist node

    Node::resetGlobalVisited();
    source_->removeSmallBranch();
    cout << "After compacting trace ..." << endl;
    cout << "# nodes \t" << Node::nodeCnt_ << endl;
    cout << "# edges \t" << Node::edgeCnt_ << endl;

    // source_->printDescendants();


    // topological order traversal and write strategy accordingly
    // use out.tellp() to get the size of current file
    unordered_map<Node*, WireInfo> info_map;
    queue<Node*> node_q;

    assert(source_->getRefCnt()==0);
    vector<int>& ei = source_->existImp_[1];
    vector<Node*>& d = source_->descendants_[1];
    intermediateID ++;
    out << "\n.names " << "w" << intermediateID << "\n1";
    info_map[source_] = WireInfo(intermediateID, vector<size_t>());

    for(size_t i=0; i < ei.size(); ++i){
        assert( ei[i]!=0 );
        if( ei[i] > 0 ){
            existID[ei[i]]++;
            out << "\n.names " << existName(ei[i]) << "\n1";
        }
    }
    
    
    for(size_t i=0; i<d.size(); ++i){
        d[i]->decreaseRefCnt();
        assert(d[i]->getRefCnt()==0);
        node_q.push(d[i]);
        intermediateID ++;
        assert(info_map.find(d[i])==info_map.end());
        info_map[d[i]] = WireInfo( intermediateID, vector<size_t>( 1, info_map[source_].first ) );
    }

    while(!node_q.empty()){
        Node* n = node_q.front(); node_q.pop();
        assert(n);

        if(out.tellp() > MAX_FILE_SIZE){
            cerr << "Warning!! strategy is too large, thus deleted" << endl;
            break;
        }
        if(n->type_==EXIST){
            vector<Node*>& d = n->descendants_[n->b_]; // max branch descendants
            vector<int>& ei = n->existImp_[n->b_];     // max branch implication
            WireInfo wi = info_map[n];
            size_t wire = wi.first;
            vector<size_t>& par_wire = wi.second;

            updateIntermediate(wire, par_wire, out);

            // update exist implication and decision
            for(size_t i=0; i < ei.size(); ++i){
                assert( ei[i]!=0 );
                if( ei[i] > 0 )
                    updateExist(ei[i], wire, out);
            }
            if(n->b_)
                updateExist( n->decVar_,  wire,  out);

            // update descendants
            for(int i=0; i<d.size(); ++i){
                assert(d[i]);
                if( info_map.find(d[i])==info_map.end() ){
                    intermediateID++;
                    info_map[d[i]] = WireInfo( intermediateID, vector<size_t>( 1, wire) );
                }
                else
                    info_map[d[i]].second.push_back(wire);
                d[i]->decreaseRefCnt();
                if(d[i]->getRefCnt()==0)
                    node_q.push(d[i]);
            }

        }
        else if(n->type_==RAND){
            WireInfo wi = info_map[n];
            size_t wire = wi.first;
            vector<size_t>& par_wire = wi.second;

            updateIntermediate(wire, par_wire, out);

            size_t w_new[2] = {0};

            w_new[0] = updateRandom(n->decVar_, wire, 1, out);
            w_new[1] = updateRandom(n->decVar_, wire, 0, out);
            intermediateID += 2;
            for(size_t k=0; k<2; ++k){
                vector<int>& ei = n->existImp_[k];
                for(size_t i=0; i < ei.size(); ++i){
                    assert( ei[i]!=0 );
                    if( ei[i] > 0 )
                        updateExist(ei[i], w_new[k], out);
                }
            }

            // update descendants
            for(size_t k=0; k<2; ++k){
                vector<Node*>& d = n->descendants_[k];
                for(int i=0; i<d.size(); ++i){
                    assert(d[i]);
                    if( info_map.find(d[i])==info_map.end() ){
                        intermediateID++;
                        info_map[d[i]] = WireInfo( intermediateID, vector<size_t>( 1, w_new[k]) );
                    }
                    else
                        info_map[d[i]].second.push_back(w_new[k]);
                    d[i]->decreaseRefCnt();
                    if(d[i]->getRefCnt()==0)
                        node_q.push(d[i]);
                }
            }
        }   
    }
    
}

void Trace::cleanMinBranch(Node* n){
    Node::resetGlobalVisited();
    n->removeSmallBranch();
}

