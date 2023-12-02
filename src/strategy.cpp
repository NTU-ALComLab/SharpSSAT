
#include "strategy.h"
#include <queue>
#include <stack>
#include <unordered_map>
#include <sstream>

#define MAX_FILE_SIZE 1 * long(1024) * long(1024 * 1024)

unsigned Node::nodeCnt_ = 0;
unsigned Node::edgeCnt_ = 0;
size_t Node::globalVisited_ = 0;

typedef pair<size_t, vector<size_t>> WireInfo; // its wire and parents wire;

bool Node::noDuplicateDescendants(Node *n)
{
    vector<Node *> &d = descendants_[curBranch_];
    for (size_t i = 0; i < d.size(); ++i)
        if (n == d[i])
            return false;
    return true;
}

void Node::removeAllDescendants(bool branch)
{
    vector<Node *> &d = descendants_[branch];
    for (size_t i = 0; i < d.size(); ++i)
    {
        assert(d[i]);
        d[i]->decreaseRefCnt();
        if (d[i]->getRefCnt() == 0)
        {
            d[i]->removeAllDescendants(0);
            d[i]->removeAllDescendants(1);
            delete d[i];
        }
        edgeCnt_--;
    }
    vector<Node *>().swap(d);
    assert(descendants_[branch].empty());
}

// delete the branch of Exist node
// such that leaves max_branch only;
void Node::removeSmallBranch()
{
    if (visited())
        return;
    if (type_ == RAND)
    {
        for (size_t i = 0; i < 2; ++i)
        {
            for (size_t j = 0; j < descendants_[i].size(); ++j)
            {
                descendants_[i][j]->removeSmallBranch();
            }
        }
    }
    else if (type_ == EXIST)
    {
        removeAllDescendants(!b_);
        for (size_t i = 0; i < descendants_[b_].size(); ++i)
        {
            Node *d = descendants_[b_][i];
            descendants_[b_][i]->removeSmallBranch();
        }
    }
    else
    { // DUMMY
        for (size_t i = 0; i < descendants_[1].size(); ++i)
            descendants_[1][i]->removeSmallBranch();
    }
    setVisited();
}

// debug
void Node::printDescendants()
{
    if (visited())
        return;
    if (type_ == EXIST)
    {
        cout << this << "\tMaxBr=" << decVar_ << (b_ ? "" : "'") << endl;
    }
    if (!descendants_[0].empty())
    {
        cout << this << "\t[L " << decVar_ << "]" << endl;
        for (size_t i = 0; i < descendants_[0].size(); ++i)
        {
            assert(descendants_[0][i]);
            cout << "Edge " << this << " -> " << descendants_[0][i] << endl;
            descendants_[0][i]->printDescendants();
        }
    }

    if (!descendants_[1].empty())
    {
        cout << this << "\t[R " << decVar_ << "]" << endl;
        for (size_t i = 0; i < descendants_[1].size(); ++i)
        {
            assert(descendants_[1][i]);
            cout << "Edge " << this << " -> " << descendants_[1][i] << endl;
            descendants_[1][i]->printDescendants();
        }
    }
    setVisited();
}

void Trace::updateExist(size_t ev, size_t w, ofstream &out)
{
    out << "\n.names"
        << " w" << w << " " << existName(ev);
    existID[ev]++;
    out << " " << existName(ev) << "\n00 0"; // e' = e v w
}

void Trace::updateIntermediate(size_t wire, vector<size_t> &par_wire, ofstream &out)
{
    // out << "\n# update intermetiate";
    out << "\n.names";
    for (size_t i = 0; i < par_wire.size(); ++i)
        out << " w" << par_wire[i];
    out << " w" << wire;
    out << "\n"
        << string(par_wire.size(), '0') << " 0";
}

// new_wire = wire & (rv' or rv)
size_t Trace::updateRandom(size_t rv, size_t wire, bool sign, ofstream &out)
{
    size_t new_wire = intermediateID + (sign ? 1 : 2);
    out << "\n.names";
    out << " w" << wire << " r" << rv << " w" << new_wire;
    out << "\n1" << (sign ? "0" : "1") << " 1";
    return new_wire;
}

void Trace::writeStrategyToFile(ofstream &out)
{
    // compact DAG, remove small branch of exist node

    Node::resetGlobalVisited();
    source_->removeSmallBranch();
    cout << "After compacting trace ..." << endl;
    cout << "# nodes \t" << Node::nodeCnt_ << endl;
    cout << "# edges \t" << Node::edgeCnt_ << endl;

    // source_->printDescendants();

    // topological order traversal and write strategy accordingly
    // use out.tellp() to get the size of current file
    unordered_map<Node *, WireInfo> info_map;
    queue<Node *> node_q;

    assert(source_->getRefCnt() == 0);
    vector<int> &ei = source_->existImp_[1];
    vector<Node *> &d = source_->descendants_[1];
    intermediateID++;
    out << "\n.names "
        << "w" << intermediateID << "\n1";
    info_map[source_] = WireInfo(intermediateID, vector<size_t>());

    for (size_t i = 0; i < ei.size(); ++i)
    {
        assert(ei[i] != 0);
        if (ei[i] > 0)
        {
            existID[ei[i]]++;
            out << "\n.names " << existName(ei[i]) << "\n1";
        }
    }

    for (size_t i = 0; i < d.size(); ++i)
    {
        d[i]->decreaseRefCnt();
        assert(d[i]->getRefCnt() == 0);
        node_q.push(d[i]);
        intermediateID++;
        assert(info_map.find(d[i]) == info_map.end());
        info_map[d[i]] = WireInfo(intermediateID, vector<size_t>(1, info_map[source_].first));
    }

    while (!node_q.empty())
    {
        Node *n = node_q.front();
        node_q.pop();
        assert(n);

        if (out.tellp() > MAX_FILE_SIZE)
        {
            cerr << "Warning!! strategy is too large, thus deleted" << endl;
            break;
        }
        if (n->type_ == EXIST)
        {
            vector<Node *> &d = n->descendants_[n->b_]; // max branch descendants
            vector<int> &ei = n->existImp_[n->b_];      // max branch implication
            WireInfo wi = info_map[n];
            size_t wire = wi.first;
            vector<size_t> &par_wire = wi.second;

            updateIntermediate(wire, par_wire, out);

            // update exist implication and decision
            for (size_t i = 0; i < ei.size(); ++i)
            {
                assert(ei[i] != 0);
                if (ei[i] > 0)
                    updateExist(ei[i], wire, out);
            }
            if (n->b_)
                updateExist(n->decVar_, wire, out);

            // update descendants
            for (int i = 0; i < d.size(); ++i)
            {
                assert(d[i]);
                if (info_map.find(d[i]) == info_map.end())
                {
                    intermediateID++;
                    info_map[d[i]] = WireInfo(intermediateID, vector<size_t>(1, wire));
                }
                else
                    info_map[d[i]].second.push_back(wire);
                d[i]->decreaseRefCnt();
                if (d[i]->getRefCnt() == 0)
                    node_q.push(d[i]);
            }
        }
        else if (n->type_ == RAND)
        {
            WireInfo wi = info_map[n];
            size_t wire = wi.first;
            vector<size_t> &par_wire = wi.second;

            updateIntermediate(wire, par_wire, out);

            size_t w_new[2] = {0};

            w_new[0] = updateRandom(n->decVar_, wire, 1, out);
            w_new[1] = updateRandom(n->decVar_, wire, 0, out);
            intermediateID += 2;
            for (size_t k = 0; k < 2; ++k)
            {
                vector<int> &ei = n->existImp_[k];
                for (size_t i = 0; i < ei.size(); ++i)
                {
                    assert(ei[i] != 0);
                    if (ei[i] > 0)
                        updateExist(ei[i], w_new[k], out);
                }
            }

            // update descendants
            for (size_t k = 0; k < 2; ++k)
            {
                vector<Node *> &d = n->descendants_[k];
                for (int i = 0; i < d.size(); ++i)
                {
                    assert(d[i]);
                    if (info_map.find(d[i]) == info_map.end())
                    {
                        intermediateID++;
                        info_map[d[i]] = WireInfo(intermediateID, vector<size_t>(1, w_new[k]));
                    }
                    else
                        info_map[d[i]].second.push_back(w_new[k]);
                    d[i]->decreaseRefCnt();
                    if (d[i]->getRefCnt() == 0)
                        node_q.push(d[i]);
                }
            }
        }
    }
}
void Trace::writeCertificate(ofstream& out, bool isUp)
{
    assert(nNode_ == 0);
    assert(source_->getRefCnt() == 0);

    // print the constants
    Node * zero = constants_[0];
    Node * one  = constants_[1];
    zero->DNNFId = 0;
    one-> DNNFId = 1;
    nNode_ = 2;
    out << "f " << zero->DNNFId<<" 0\n";
    out << "t " << one->DNNFId<<" 0\n";

    writeCertificateRecur(out, source_, isUp);
}
void Trace::writeCertificateRecur(ofstream& out, Node *node, bool isUp)
{
    int curr_branch = 0;
    int child[2] = {-1, -1};
    assert(node != nullptr);

    if (node->type_ == DUMMY)
    {
        if (node == constants_[0] || node == constants_[1])
            return;
        else
        {
            assert(node == source_);
            ++curr_branch;
        }
    }
    // Create decision node
    assert(node->DNNFId == -1);
    node->DNNFId = nNode_++;
    out<<"o "<<node->DNNFId<<" 0\n";
    for (; curr_branch < 2; ++curr_branch)
    {
        vector<int> &ei = node->existImp_[curr_branch];
        vector<int> &ri = node->randomImp_[curr_branch];
        vector<int> &pl = node->pureLits_[curr_branch];
        vector<Node *> &d = node->descendants_[curr_branch];

        if( curr_branch == 1 && node->hasEarlyReturn_ )
            child[curr_branch] = (isUp ? constants_[1]->DNNFId : constants_[0]->DNNFId );
        else
        {
            assert(d.size());
            // create used decision nodes
            for (Node *dec : d)
            {
                if (dec->DNNFId == -1)
                    writeCertificateRecur(out, dec, isUp);
                assert(dec->DNNFId <= int(nNode_));
            }
            
            if (d.size() > 1)   // curr_node[curr_branch] is an AND-node
            {
                // Create and record new node
                child[curr_branch] = nNode_++;
                int andID = child[curr_branch];
                out << "a " << andID <<" 0\n ";

                nEdge_ += d.size();

                for (Node *dec : d)
                    out<< andID <<" "<< dec->DNNFId <<" 0\n";
            }
            else   // Single decision node
                child[curr_branch] = d[0]->DNNFId;
        }

        // print edge
        nEdge_++;
        out<< node->DNNFId <<" "<< child[curr_branch] << " ";
        out << ( curr_branch ? "" : "-" ) << node->decVar_;
        for (int l : ei)    out<<" "<<l;
        for (int l : ri)    out<<" "<<l;
        if (!isUp ){ for (int l : pl) out<<" "<<l;  }    // only print pure literal for lower trace
        out<<" 0\n";
    }
}

// Save Trace as dec-DNNF
void Trace::writeDNNF(ofstream &out)
{
    // Use stringstream to buffer the content and add header at the end
    unsigned nVar = existID.size() - 1;
    // cout << nNode_ << endl;
    assert(nNode_ == 0);
    assert(lit2NodeId_.empty());
    lit2NodeId_.resize((nVar + 1) << 1, -1);
    // Node::resetGlobalVisited();

    // topological order traversal and write strategy accordingly
    // use out.tellp() to get the size of current file
    // unordered_map<Node *, WireInfo> info_map;
    assert(source_->getRefCnt() == 0);

    // Print constant nodes regardless and assign their id
    ss << "O 0 0" << endl;
    ss << "A 0" << endl;
    constants_[0]->DNNFId = 0;
    constants_[1]->DNNFId = 1;
    nNode_ = 2;
    writeDNNFRecur(source_);
    out << "nnf " << nNode_ << ' ' << nEdge_ << ' ' << nVar << endl;
    out << ss.rdbuf();
}

void Trace::writeDNNFRecur(Node *n)
{
    int curr_branch = 0;
    int child[2] = {-1, -1};
    assert(n != nullptr);
    if (n->type_ == DUMMY)
    {
        if (n == constants_[0] || n == constants_[1])
        {
            return;
        }
        else
        {
            assert(n == source_);
            ++curr_branch;
        }
    }
    for (; curr_branch < 2; ++curr_branch)
    {
        vector<int> &ei = n->existImp_[curr_branch];
        vector<int> &ri = n->randomImp_[curr_branch];
        vector<Node *> &d = n->descendants_[curr_branch];

        // create leaf node for literals
        for (int l : ei)
        {
            assert(l);
            int l_id = abs(l) * 2 + (l < 0);
            if (lit2NodeId_[l_id] == -1)
            {
                lit2NodeId_[l_id] = nNode_;
                ++nNode_;
                ss << "L " << l << endl;
            }
        }
        for (int l : ri)
        {
            assert(l);
            int l_id = abs(l) * 2 + (l < 0);
            if (lit2NodeId_[l_id] == -1)
            {
                lit2NodeId_[l_id] = nNode_;
                ++nNode_;
                ss << "L " << l << endl;
            }
        }
        // create used decision nodes
        for (Node *dec : d)
        {
            if (dec->DNNFId == -1)
            {
                writeDNNFRecur(dec);
            }
            assert(dec->DNNFId <= int(nNode_));
        }
        // curr_node[curr_branch] is an AND-node
        if (!ei.empty() || !ri.empty() || d.size() > 1)
        {
            // Create and record new node
            child[curr_branch] = nNode_;
            ++nNode_;
            size_t n = ei.size() + ri.size() + d.size();
            nEdge_ += n;
            int cnt = 0;
            ss << "A " << n << ' ';
            for (int l : ei)
            {
                assert(l);
                int l_id = abs(l) * 2 + (l < 0);
                ss << lit2NodeId_[l_id];
                ++cnt;
                if (cnt != n)
                {
                    ss << ' ';
                }
            }
            for (int l : ri)
            {
                assert(l);
                int l_id = abs(l) * 2 + (l < 0);
                ss << lit2NodeId_[l_id];
                ++cnt;
                if (cnt != n)
                {
                    ss << ' ';
                }
            }
            for (Node *dec : d)
            {
                ss << dec->DNNFId;
                ++cnt;
                if (cnt != n)
                {
                    ss << ' ';
                }
            }
            ss << endl;
        }
        // Single decision node
        else
        {
            // Original empty decision is replaced with constant node
            assert(d.size() == 1);
            // if(d.size() == 1)
            //     child[curr_branch] = d[0]->DNNFId;
            // else
            //     child[curr_branch] = -50;
            child[curr_branch] = d[0]->DNNFId;
        }
    }
    // Create decision node
    if (n->type_ != DUMMY)
    {
        assert(n->DNNFId == -1);
        n->DNNFId = nNode_;
        ++nNode_;
        nEdge_ += 2;
        ss << "D " << n->decVar_ <<' ' << child[0] << ' ' << child[1] << endl;
    }
}

void Trace::cleanMinBranch(Node *n)
{
    Node::resetGlobalVisited();
    n->removeSmallBranch();
}
