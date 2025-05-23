/*
 * component_management.cpp
 *
 *  Created on: Aug 23, 2012
 *      Author: Marc Thurley
 */

#include "component_management.h"

#include <algorithm>
#include <sys/sysinfo.h>
#include <fstream>
#include <stdio.h>
#include <stdlib.h> 
ComponentCache::ComponentCache(SolverConfiguration &conf,
		DataAndStatistics &statistics) :
		config_(conf), statistics_(statistics) {
}

void ComponentCache::init() {
	table_.clear();
	entry_base_.clear();
	entry_base_.reserve(2000000);
	entry_base_.push_back(new CachedComponent()); // dummy Element
	table_.resize(900001, NULL);
	free_entry_base_slots_.clear();
	free_entry_base_slots_.reserve(10000);

	struct sysinfo info;
	sysinfo(&info);

	min_free_ram_ = info.totalram / 20;
	unsigned long max_cache_bound = 95 * (info.freeram / 100);

	if (config_.maximum_cache_size_bytes == 0) {
		config_.maximum_cache_size_bytes = max_cache_bound;
	}

	if (config_.maximum_cache_size_bytes > info.freeram) {
		cout << endl <<" WARNING: Maximum cache size larger than free RAM available" << endl;
		cout << " Free RAM " << info.freeram / 1000000 << "MB" << endl;
	}

	cout << "Maximum cache size:\t"
			<< config_.maximum_cache_size_bytes / 1000000 << " MB" << endl
			<< endl;

	recompute_bytes_memory_usage();
}

CacheEntryID ComponentCache::createEntryFor(Component &comp,
		unsigned stack_id) {
	my_time_++;
	CacheEntryID id;

	if (statistics_.cache_bytes_memory_usage_
			>= config_.maximum_cache_size_bytes) {
		deleteEntries();
	}

	assert(
			statistics_.cache_bytes_memory_usage_ < config_.maximum_cache_size_bytes);
	if (free_entry_base_slots_.empty()) {
		if (entry_base_.capacity() == entry_base_.size()) {
			entry_base_.reserve(2 * entry_base_.size());
		}
		entry_base_.push_back(new CachedComponent(comp));
		id = entry_base_.size() - 1;
	} else {
		id = free_entry_base_slots_.back();
		assert(id < entry_base_.size());
		assert(entry_base_[id] == nullptr);
		free_entry_base_slots_.pop_back();
		entry_base_[id] = new CachedComponent(comp);
	}
	entry_base_[id]->setComponentStackID(stack_id);
	entry_base_[id]->set_creation_time(my_time_);

	assert(entry_base_[id]->first_descendant() == 0);
	assert(entry_base_[id]->next_sibling() == 0);
	statistics_.cache_bytes_memory_usage_ += entry_base_[id]->SizeInBytes();
	statistics_.sum_size_cached_components_ += entry_base_[id]->num_variables();
	statistics_.num_cached_components_++;

#ifdef DEBUG
    for (unsigned u = 2; u < entry_base_.size(); u++)
          if (entry_base_[u] != nullptr) {
            assert(entry_base_[u]->father() != id);
            assert(entry_base_[u]->first_descendant() != id);
            assert(entry_base_[u]->next_sibling() != id);
          }
#endif
	return id;
}

void ComponentCache::test_descendantstree_consistency() {
	for (unsigned id = 2; id < entry_base_.size(); id++)
		if (entry_base_[id] != nullptr) {
			CacheEntryID act_child = entry(id).first_descendant();
			while (act_child) {
				CacheEntryID next_child = entry(act_child).next_sibling();
				assert(entry(act_child).father() == id);

				act_child = next_child;
			}
			CacheEntryID father = entry(id).father();
			CacheEntryID act_sib = entry(father).first_descendant();
#ifndef NDEBUG
			bool found = false;
#endif
			while (act_sib) {
				CacheEntryID next_sib = entry(act_sib).next_sibling();
#ifndef NDEBUG
				if (act_sib == id)
					found = true;
#endif
				act_sib = next_sib;
			}
			assert(found);
		}
}

unsigned long ComponentCache::recompute_bytes_memory_usage() {
	statistics_.cache_bytes_memory_usage_ = sizeof(ComponentCache)
			+ sizeof(CacheBucket *) * table_.capacity();
	for (auto pbucket : table_)
		if (pbucket != nullptr)
			statistics_.cache_bytes_memory_usage_ +=
					pbucket->getBytesMemoryUsage();
	for (auto pentry : entry_base_)
		if (pentry != nullptr) {
			statistics_.cache_bytes_memory_usage_ += pentry->SizeInBytes();
		}
	return statistics_.cache_bytes_memory_usage_;
}

// FIXME for ssat

bool ComponentCache::requestProbOf(Component &comp, double& prob, Node*& n) {
	n = NULL;
	CachedComponent &packedcomp = entry(comp.id());

	unsigned int v = clip(packedcomp.hashkey());
	if (!isBucketAt(v))
		return false;

	CachedComponent *pcomp;
	statistics_.num_cache_look_ups_++;

	for (auto it = table_[v]->begin(); it != table_[v]->end(); it++) {
		pcomp = &entry(*it);
		if (packedcomp.hashkey() == pcomp->hashkey()
				&& pcomp->equals(packedcomp)) {
			statistics_.num_cache_hits_++;
			statistics_.sum_cache_hit_sizes_ += pcomp->num_variables();
			prob = pcomp->sat_prob();
			n = pcomp->get_node();
			//pComp->set_creation_time(my_time_);
			return true;
		}
	}
	return false;
}

bool ComponentCache::requestValueOf(Component &comp, mpz_class &rn) {
	CachedComponent &packedcomp = entry(comp.id());

	unsigned int v = clip(packedcomp.hashkey());
	if (!isBucketAt(v))
		return false;

	CachedComponent *pcomp;
	statistics_.num_cache_look_ups_++;

	for (auto it = table_[v]->begin(); it != table_[v]->end(); it++) {
		pcomp = &entry(*it);
		if (packedcomp.hashkey() == pcomp->hashkey()
				&& pcomp->equals(packedcomp)) {
			statistics_.num_cache_hits_++;
			statistics_.sum_cache_hit_sizes_ += pcomp->num_variables();
			rn = pcomp->model_count();
			//pComp->set_creation_time(my_time_);
			return true;
		}
	}
	return false;
}

bool ComponentCache::deleteEntries() {
	assert(
			statistics_.cache_bytes_memory_usage_ >= config_.maximum_cache_size_bytes);

	vector<double> scores;
	for (auto it = entry_base_.begin() + 1; it != entry_base_.end(); it++)
		if (*it != nullptr && (*it)->deletable()) {
			scores.push_back((double) (*it)->creation_time());
		}
	sort(scores.begin(), scores.end());
	double cutoff = scores[scores.size() / 2];

	//cout << "cutoff" << cutoff  << " entries: "<< entry_base_.size()<< endl;

	// first : go through the EntryBase and mark the entries to be deleted as deleted (i.e. EMPTY
	// note we start at index 2,
	// since index 1 is the whole formula,
	// should always stay here!
	for (unsigned id = 2; id < entry_base_.size(); id++)
		if (entry_base_[id] != nullptr && entry_base_[id]->deletable()) {
			double as = (double) entry_base_[id]->creation_time();
			if (as <= cutoff) {
				removeFromDescendantsTree(id);
				eraseEntry(id);
			}
		}
	// then go through the Hash Table and erase all Links to empty entries
	for (auto pbucket : table_)
		if (pbucket != nullptr) {
			for (auto bt = pbucket->rbegin(); bt != pbucket->rend(); bt++) {
				if (entry_base_[*bt] == nullptr) {
					*bt = pbucket->back();
					pbucket->pop_back();
				}
			}
		}
#ifdef DEBUG
	test_descendantstree_consistency();
#endif

	statistics_.sum_size_cached_components_ = 0;
	for (unsigned id = 2; id < entry_base_.size(); id++)
		if (entry_base_[id] != nullptr) {
			statistics_.sum_size_cached_components_ +=
					entry_base_[id]->num_variables();
		}

	statistics_.num_cached_components_ = entry_base_.size();
	statistics_.cache_bytes_memory_usage_ = recompute_bytes_memory_usage();

	//cout << " \t entries: "<< entry_base_.size() - free_entry_base_slots_.size()<< endl;
	return true;
}

void ComponentAnalyzer::initialize(LiteralIndexedVector<Literal> & literals,
		vector<LiteralID> &lit_pool, vector<QType>& var_type) {

	cache_.init();
	max_variable_id_ = literals.end_lit().var() - 1;
	var2Q_ = var_type;

	variables_seen_ = new CA_SearchState[max_variable_id_ + 1];
	pos_var_seen_ = new unsigned[max_variable_id_+1];
	neg_var_seen_ = new unsigned[max_variable_id_+1];
	component_search_stack_.reserve(max_variable_id_ + 1);
	var_frequency_scores_.resize(max_variable_id_ + 1, 0);
	variable_occurrence_lists_pool_.clear();
	variable_link_list_offsets_.resize(max_variable_id_ + 1, 0);
	memset(variables_seen_, CA_NIL,
			sizeof(CA_SearchState) * (max_variable_id_ + 1));
	memset(pos_var_seen_, 0,
			sizeof(unsigned) * (max_variable_id_ + 1));
	memset(neg_var_seen_, 0,
			sizeof(unsigned) * (max_variable_id_ + 1));

	literal_pool_.reserve(lit_pool.size());



	vector<vector<ClauseOfs> > occs_(max_variable_id_ + 1);
	vector<vector<ClauseOfs> > pos_occs_(max_variable_id_+1);
	vector<vector<ClauseOfs> > neg_occs_(max_variable_id_+1);
	ClauseOfs current_clause_ofs = 0;
	max_clause_id_ = 0;
	unsigned curr_clause_length = 0;
	cls_id_to_Ofs_.push_back(0); // dummy clsOfs

	// long clause
	for (auto it_lit = lit_pool.begin(); it_lit < lit_pool.end(); it_lit++) {
		if (*it_lit == SENTINEL_LIT) {

			if (it_lit + 1 == lit_pool.end()) {
				literal_pool_.push_back(SENTINEL_LIT);
				break;
			}

			max_clause_id_++;
			literal_pool_.push_back(SENTINEL_LIT);
			for (unsigned i = 0; i < CAClauseHeader::overheadInLits(); i++)
				literal_pool_.push_back(0);
			current_clause_ofs = literal_pool_.size();
			getHeaderOf(current_clause_ofs).clause_id = max_clause_id_;
			cls_id_to_Ofs_.push_back(current_clause_ofs);
			assert(cls_id_to_Ofs_.size()-1==max_clause_id_);
			it_lit += ClauseHeader::overheadInLits();
			curr_clause_length = 0;
		} else {
			assert(it_lit->var() <= max_variable_id_);
			literal_pool_.push_back(*it_lit);
			curr_clause_length++;
			occs_[it_lit->var()].push_back(current_clause_ofs);
			if(it_lit->sign()) { 
				pos_occs_[it_lit->var()].push_back(current_clause_ofs);
			}
			else{
				neg_occs_[it_lit->var()].push_back(current_clause_ofs);
			}
		}
	}

	clauses_seen_ = new CA_SearchState[max_clause_id_ + 1];
	memset(clauses_seen_, CA_NIL,
			sizeof(CA_SearchState) * (max_clause_id_ + 1));
	// the unified link list
	unified_variable_links_lists_pool_.clear();
	unified_variable_links_lists_pool_.push_back(0);
	unified_variable_links_lists_pool_.push_back(0);
	for (unsigned v = 1; v < occs_.size(); v++) {
		variable_link_list_offsets_[v] = unified_variable_links_lists_pool_.size();
		// positive occurence in binary clause
		for (auto l : literals[LiteralID(v, true)].binary_links_)
			if (l != SENTINEL_LIT) {
				unified_variable_links_lists_pool_.push_back(l.toInt());
			}
		unified_variable_links_lists_pool_.push_back(0);
		// negative occurence in binary clause
		for (auto l : literals[LiteralID(v, false)].binary_links_)
			if (l != SENTINEL_LIT) {
				unified_variable_links_lists_pool_.push_back(l.toInt());
			}
		unified_variable_links_lists_pool_.push_back(0);
		unified_variable_links_lists_pool_.insert(
			unified_variable_links_lists_pool_.end(), pos_occs_[v].begin(),
			pos_occs_[v].end());
		unified_variable_links_lists_pool_.push_back(0);
		unified_variable_links_lists_pool_.insert(
			unified_variable_links_lists_pool_.end(), neg_occs_[v].begin(),
			neg_occs_[v].end());
		unified_variable_links_lists_pool_.push_back(0);
	}

	// BEGIN CACHE INIT
	CachedComponent::adjustPackSize(max_variable_id_, max_clause_id_);
	initializeComponentStack();
}

bool ComponentAnalyzer::recordRemainingCompsFor(StackLevel &top) {
	Component & super_comp = superComponentOf(top);
	// FIXME SSAT
	static mpz_class tmp_model_count;
	double 	tmp_sat_prob;
	Node* 	node;

	memset(clauses_seen_, CA_NIL,
			sizeof(CA_SearchState) * (max_clause_id_ + 1));
	memset(variables_seen_, CA_NIL,
			sizeof(CA_SearchState) * (max_variable_id_ + 1));
	memset(pos_var_seen_, 0,
			sizeof(unsigned) * (max_variable_id_ + 1));
	memset(neg_var_seen_, 0,
			sizeof(unsigned) * (max_variable_id_ + 1));

	for (auto vt = super_comp.varsBegin(); *vt != varsSENTINEL; vt++) {
		if (isActive(*vt)) {
			variables_seen_[*vt] = CA_IN_SUP_COMP;
			var_frequency_scores_[*vt] = 0;
		}
	}

	for (auto itCl = super_comp.clsBegin(); *itCl != clsSENTINEL; itCl++)
		clauses_seen_[*itCl] = CA_IN_SUP_COMP;

	unsigned new_comps_start_ofs = component_stack_.size();

	for (auto vt = super_comp.varsBegin(); *vt != varsSENTINEL; vt++)
		if (variables_seen_[*vt] == CA_IN_SUP_COMP) {
			recordComponentOf(*vt, top);
			if (component_search_stack_.size() == 1) {
				// FIXME for ssat
				if(!config_.ssat_solving)
					top.includeSolution(2);
				else 
					top.includeSatProb(1); //FIXME
				variables_seen_[*vt] = CA_IN_OTHER_COMP;
			} else {
				/////////////////////////////////////////////////
				// BEGIN store variables and clauses in component_stack_.back()
				// protocol is: variables first, then clauses
				/////////////////////////////////////////////////
				component_stack_.push_back(new Component());
				component_stack_.back()->reserveSpace(
						component_search_stack_.size(),
						super_comp.numLongClauses());

				for (auto v_it = super_comp.varsBegin(); *v_it != varsSENTINEL;
						v_it++)
					if (variables_seen_[*v_it] == CA_SEEN) { //we have to put a var into our component
						component_stack_.back()->addVar(*v_it);
						variables_seen_[*v_it] = CA_IN_OTHER_COMP;
					}
				component_stack_.back()->closeVariableData();

				for (auto it_cl = super_comp.clsBegin(); *it_cl != clsSENTINEL;
						it_cl++)
					if (clauses_seen_[*it_cl] == CA_SEEN) {
						component_stack_.back()->addCl(*it_cl);
						clauses_seen_[*it_cl] = CA_IN_OTHER_COMP;
					}
				component_stack_.back()->closeClauseData();
				
				// cout << "Record Component " << component_stack_.size()-1 << " ";
				// component_stack_.back()->print();
				/////////////////////////////////////////////////
				// END store variables in resComp
				/////////////////////////////////////////////////
				if (config_.perform_component_caching) {
					CacheEntryID id = cache_.createEntryFor(
							*component_stack_.back(),
							component_stack_.size() - 1);
					if (id != 0) {
						component_stack_.back()->set_id(id);
						// set up the father
						assert(cache_.hasEntry(id));
						assert(cache_.hasEntry(super_comp.id()));
						// FIXME for ssat
						if(config_.ssat_solving){
							if (cache_.requestProbOf(*component_stack_.back(),
								tmp_sat_prob, node)) {
								
								top.includeSatProb(tmp_sat_prob);
								if(config_.strategy_generation || config_.compile_DNNF || config_.certificate_generation){
									assert(node);
									assert(top.getNode()!=node);
									top.getNode()->addDescendant(node);
								}
								cache_.eraseEntry(id);
								delete component_stack_.back();
								component_stack_.pop_back();
							}
							else {
								cache_.entry(id).set_father(super_comp.id());
								cache_.add_descendant(super_comp.id(), id);
							}
						}
						else{
							if (cache_.requestValueOf(*component_stack_.back(),
								tmp_model_count)) {
								top.includeSolution(tmp_model_count);
								cache_.eraseEntry(id);
								delete component_stack_.back();
								component_stack_.pop_back();
							} else {
								cache_.entry(id).set_father(super_comp.id());
								cache_.add_descendant(super_comp.id(), id);
							}
						}
					}
				}
			}
		}

	top.set_unprocessed_components_end(component_stack_.size());

	assert(new_comps_start_ofs <= component_stack_.size());

	//sort the remaining components for processing
	for (unsigned i = new_comps_start_ofs; i < component_stack_.size(); i++)
		for (unsigned j = i + 1; j < component_stack_.size(); j++) {
			if (component_stack_[i]->num_variables()
					< component_stack_[j]->num_variables())
				swap(component_stack_[i], component_stack_[j]);
		}
	return true;
}

void ComponentAnalyzer::recordComponentOf(const VariableIndex var, StackLevel& top) {
	component_search_stack_.clear();
	component_search_stack_.push_back(var);

	variables_seen_[var] = CA_SEEN;


	vector<VariableIndex>::const_iterator itVEnd;

	static Vars pure_literal_stack_;
	if (config_.perform_pure_literal) {
		pure_literal_stack_.clear();
		pure_literal_stack_.reserve(max_variable_id_ + 1);
	}

	for (auto vt = component_search_stack_.begin();
			vt != component_search_stack_.end(); vt++) {
		// the for-loop is applicable here because componentSearchStack.capacity() == countAllVars()
		//BEGIN traverse binary clauses
		// cout << "record reachability for " << *vt << endl;
		assert(isActive(*vt));
		// NOTE
		int *pvar = beginOfLinkList(*vt);

		// traverse positive and negatives occurence of *vt
		for(int i=0; i<2; ++i){
			for (; *pvar!=0; pvar++) {
				LiteralID lit = LiteralID(*pvar);
				if (variables_seen_[lit.var()] == CA_IN_SUP_COMP) {
					assert(isActive(lit.var()));
					component_search_stack_.push_back(lit.var());
					variables_seen_[lit.var()] = CA_SEEN;
					var_frequency_scores_[lit.var()]++;
					var_frequency_scores_[*vt]++;
				}
				if(config_.perform_pure_literal){
					if(variables_seen_[lit.var()] == CA_SEEN){
						(i==0) ? (pos_var_seen_[*vt]++) : (neg_var_seen_[*vt]++) ;
					}
				}	
			}
			pvar++;
		}
		//END traverse binary clauses

		// start traversing links to long clauses
		// not that that list starts right after the 0 termination of the prvious list
		// hence  pcl_ofs = pvar + 1
		int* pcl_ofs = pvar;
		for(int i=0; i<2; ++i){
			for (; *pcl_ofs != 0; pcl_ofs++) {
				ClauseIndex clID = getClauseID(*pcl_ofs);
				if (clauses_seen_[clID] == CA_IN_SUP_COMP) {
					itVEnd = component_search_stack_.end();
					for (auto itL = beginOfClause(*pcl_ofs); *itL != SENTINEL_LIT;
							itL++) {
						assert(itL->var() <= max_variable_id_);
						if (variables_seen_[itL->var()] == CA_NIL) { //i.e. the variable is not active
							if (isResolved(*itL))
								continue;
							//BEGIN accidentally entered a satisfied clause: undo the search process
							while (component_search_stack_.end() != itVEnd) {
								assert(
										component_search_stack_.back() <= max_variable_id_);
								variables_seen_[component_search_stack_.back()] =
										CA_IN_SUP_COMP;
								component_search_stack_.pop_back();
							}
							clauses_seen_[clID] = CA_NIL;
							for (auto itX = beginOfClause(*pcl_ofs); itX != itL;
									itX++) {
								if (var_frequency_scores_[itX->var()] > 0)
									var_frequency_scores_[itX->var()]--;
							}
							//END accidentally entered a satisfied clause: undo the search process
							break;
						} else {
							var_frequency_scores_[itL->var()]++;
							if (variables_seen_[itL->var()] == CA_IN_SUP_COMP) {
								// cout << "long reach ";  itL->print(); cout << endl;
								variables_seen_[itL->var()] = CA_SEEN;
								component_search_stack_.push_back(itL->var());
							}
						}
					}
					if (clauses_seen_[clID] == CA_NIL)
						continue;
					clauses_seen_[clID] = CA_SEEN;
					
				}
				// pure literal
				if( clauses_seen_[clID]==CA_SEEN){
					//FIXME bottle-neck here
					(i==0) ? (pos_var_seen_[*vt]++) : (neg_var_seen_[*vt]++) ;
				}
			}
			pcl_ofs++;
		}
		
		
		if (config_.perform_pure_literal) {
			bool is_pos = (neg_var_seen_[*vt] == 0);
			bool is_neg = (pos_var_seen_[*vt] == 0);
			if (is_pos ^ is_neg) {
				if (var2Q_[*vt] == EXISTENTIAL) pure_literal_stack_.push_back(*vt);
			}
		}
	}

	if (config_.perform_pure_literal) for (auto vt = pure_literal_stack_.begin();
	vt != pure_literal_stack_.end(); ++vt) {
		assert(var2Q_[*vt] == EXISTENTIAL);

		int is_pos = (neg_var_seen_[*vt] == 0);
		if (is_pos && pos_var_seen_[*vt] == 0) continue;

		variables_seen_[*vt] = CA_NIL;
		if(config_.strategy_generation || config_.compile_DNNF){
			top.getNode()->addExistImplication(is_pos ? *vt : -(*vt));
		}
		if(config_.certificate_generation)
			top.getNode()->addPureLiteral(is_pos ? *vt : -(*vt));
		int* pvar = beginOfLinkList(*vt);
		for (int is_neg_link = 0; is_neg_link < 2; is_neg_link++) {
			if (is_pos == is_neg_link) while (*pvar != 0) ++pvar;
			else for (; *pvar != 0; ++pvar) { // remove binary linked literals counts
				LiteralID lit = LiteralID(*pvar);
				if (variables_seen_[lit.var()] != CA_SEEN || var2Q_[lit.var()] != EXISTENTIAL) continue;
				if (lit.sign()) {
					if (--pos_var_seen_[lit.var()] == 0 && neg_var_seen_[lit.var()] != 0) pure_literal_stack_.push_back(lit.var());
				}
				else {
					if (--neg_var_seen_[lit.var()] == 0 && pos_var_seen_[lit.var()] != 0) pure_literal_stack_.push_back(lit.var());
				}
			}
			++pvar;
		}
		// binary clauses processed, start processing long clauses
		int* pcl_ofs = pvar;
		for (int is_neg_link = 0; is_neg_link < 2; is_neg_link++) {
			if (is_neg_link == 0 && !is_pos) while (*pcl_ofs != 0) ++pcl_ofs;
			else if (is_neg_link && is_pos) break;
			else for (; *pcl_ofs != 0; ++pcl_ofs) { // remove satisfied long clause literals counts
				ClauseIndex clause_id = getClauseID(*pcl_ofs);
				if (clauses_seen_[clause_id] != CA_SEEN) continue;
				clauses_seen_[clause_id] = CA_NIL;
				for (auto it_lit = beginOfClause(*pcl_ofs); *it_lit != SENTINEL_LIT; ++it_lit) {
					if (variables_seen_[it_lit->var()] != CA_SEEN || var2Q_[it_lit->var()] != EXISTENTIAL) continue;
					if (it_lit->sign()) {
						if (--pos_var_seen_[it_lit->var()] == 0 && neg_var_seen_[it_lit->var()] != 0) pure_literal_stack_.push_back(it_lit->var());
					}
					else {
						if (--neg_var_seen_[it_lit->var()] == 0 && pos_var_seen_[it_lit->var()] != 0) pure_literal_stack_.push_back(it_lit->var());
					}
				}
			}
			++pcl_ofs;
		}
	}
}

void ComponentAnalyzer::initializeComponentStack() {
	component_stack_.clear();
	component_stack_.reserve(max_variable_id_ + 2);
	component_stack_.push_back(new Component());
	component_stack_.push_back(new Component());
	assert(component_stack_.size() == 2);
	component_stack_.back()->createAsDummyComponent(max_variable_id_,
			max_clause_id_, literal_values_);
	CacheEntryID id = cache_.createEntryFor(*component_stack_.back(),
			component_stack_.size() - 1);
	component_stack_.back()->set_id(id);
	assert(id == 1);
}

void ComponentAnalyzer::removeAllCachePollutionsOf(StackLevel &top) {
	if (!config_.perform_component_caching)
		return;
	// all processed components are found in
	// [top.currentRemainingComponent(), component_stack_.size())
	// first, remove the list of descendants from the father
	assert(top.remaining_components_ofs() <= component_stack_.size());
	assert(top.super_component() != 0);
	assert(cache_.hasEntry(superComponentOf(top).id()));
	if (top.remaining_components_ofs() == component_stack_.size())
		return;

	for (unsigned u = top.remaining_components_ofs();
			u < component_stack_.size(); u++) {
		assert(cache_.hasEntry(component_stack_[u]->id()));
		cache_.cleanPollutionsInvolving(component_stack_[u]->id());
	}

#ifdef DEBUG
	cache_.test_descendantstree_consistency();
#endif
}

void ComponentAnalyzer::pureEliminate(VariableIndex var, vector<ClauseOfs>& occur){
	// TODO
	// 1. set var NIL
	assert(var2Q_[var]==EXISTENTIAL);
	variables_seen_[var] = CA_NIL;
	for(size_t i=0; i<occur.size(); ++i)
		clauses_seen_[occur[i]] = CA_NIL;
}

void ComponentAnalyzer::pureEliminate(VariableIndex var, int* start_ofs){
	assert(var2Q_[var]==EXISTENTIAL);
	variables_seen_[var] = CA_NIL;
	for (auto pcl_ofs = start_ofs; *pcl_ofs != SENTINEL_CL; pcl_ofs++) {
		ClauseIndex clID = getClauseID(*pcl_ofs);
		if(clauses_seen_[clID]==CA_SEEN)
			clauses_seen_[clID] = CA_NIL;
	}
}

// bool ComponentAnalyzer::satSolve(Component* pureComp){
// 	vector<bool> occur_var;
// 	vector<bool> var_visit;
// 	unsigned bin_cls_cnt = 0;
// 	vector<pair<int, int>> bin_cls;
// 	occur_var.push_back(0);
// 	var_visit.push_back(0);


// 	const string cnf = "tmp.cnf";
// 	const string log = "tmp.log";
// 	FILE* cnf_ptr = fopen("tmp.cnf", "w");
	
// 	for(auto v = pureComp->varsBegin(); *v!=varsSENTINEL; ++v ){
// 		if(occur_var.size()-1 < *v){
// 			occur_var.resize(*v+1);
// 			var_visit.resize(*v+1);
// 		}
// 		occur_var[*v] = 1;
// 	}

// 	for(auto v = pureComp->varsBegin(); *v!=varsSENTINEL; ++v ){

// 		int *pvar = beginOfLinkList(*v);

// 		// traverse positive occurence of *vt
// 		for(int i=0; i<2; ++i){
// 			for (; *pvar!=0; pvar++) {
// 				LiteralID lit = LiteralID(*pvar);
// 				if( lit.var()>occur_var.size()-1 ) continue;
// 				if (var_visit[lit.var()] == 0 && occur_var[lit.var()]) {
// 					bin_cls.push_back( pair<int, int>( ((i==0) ? *v : -*v) , lit.toInt() ) );
// 					bin_cls_cnt ++;
// 				}
// 			}
// 			pvar++;
// 		}
// 		var_visit[*v] = 1;
// 	}
// 	fprintf(cnf_ptr, "p cnf %d %d\n", occur_var.size()-1, bin_cls_cnt+pureComp->numLongClauses());
// 	// cout << "p cnf " << occur_var.size()-1 << " " << bin_cls_cnt + pureComp->numLongClauses() << endl;


// 	for(auto cl_id = pureComp->clsBegin(); *cl_id!=clsSENTINEL; ++cl_id){
// 		ClauseOfs clsOfs = cls_id_to_Ofs_[*cl_id];
// 		for(auto itL=beginOfClause(clsOfs); *itL!=SENTINEL_LIT; ++itL){
// 			if(var_visit[itL->var()]){
// 				// cout << itL->toInt() << " ";
// 				fprintf(cnf_ptr, "%d ", itL->toInt());
// 			}
// 		}
// 		// cout << "0\n";
// 		fprintf(cnf_ptr, "0\n");
// 	}
// 	for(int i=0; i<bin_cls_cnt; ++i){
// 		// cout << bin_cls[i].first << " " << bin_cls[i].second << " 0\n";
// 		fprintf(cnf_ptr, "%d %d 0\n", bin_cls[i].first, bin_cls[i].second);
// 	}
// 	fclose(cnf_ptr);

// 	// call minisat
// 	int length = 1024;
// 	char cmd[length], tmp_str[length]; 
// 	sprintf(cmd, "bin/MiniSat tmp.cnf > tmp.log");
// 	if ( system(cmd) < 0 ) {
//         fprintf(stderr, "ERROR! Problems with MiniSat execution...\n");
//         exit(124);
//     }


// 	FILE* fp = fopen("tmp.log", "r");
// 	while(!feof(fp))
// 		fgets(tmp_str, 1024, fp);

// 	fclose(fp);
// 	if( strcmp(tmp_str, "SATISFIABLE\n")==0 ){
// 		return true;
// 	}
// 	else{
// 		assert(strcmp(tmp_str, "UNSATISFIABLE\n")==0);
// 		return false;
// 	}

// }
