/*
 * component_types.cpp
 *
 *  Created on: Aug 23, 2012
 *      Author: Marc Thurley
 */

#include "component_types.h"

unsigned DiffPackedComponent::_bits_per_clause = 0;
unsigned DiffPackedComponent::_bits_per_variable = 0; // bitsperentry
unsigned DiffPackedComponent::_variable_mask = 0;
unsigned DiffPackedComponent::_clause_mask = 0; // bitsperentry

void DiffPackedComponent::adjustPackSize(unsigned int maxVarId,
    unsigned int maxClId) {
  _bits_per_variable = (unsigned int) ceil(
      log((double) maxVarId + 1) / log(2.0));
  _bits_per_clause = (unsigned int) ceil(log((double) maxClId + 1) / log(2.0));

  _variable_mask = _clause_mask = 0;
  for (unsigned int i = 0; i < _bits_per_variable; i++)
    _variable_mask = (_variable_mask << 1) + 1;
  for (unsigned int i = 0; i < _bits_per_clause; i++)
    _clause_mask = (_clause_mask << 1) + 1;
}


unsigned BasePackedComponent::_bits_per_clause = 0;
unsigned BasePackedComponent::_bits_per_variable = 0; // bitsperentry
unsigned BasePackedComponent::_variable_mask = 0;
unsigned BasePackedComponent::_clause_mask = 0; // bitsperentry
unsigned BasePackedComponent::_debug_static_val=0;
unsigned BasePackedComponent::_bits_of_data_size=0;
unsigned BasePackedComponent::_data_size_mask = 0;


void BasePackedComponent::adjustPackSize(unsigned int maxVarId,
    unsigned int maxClId) {

  _bits_per_variable = log2(maxVarId) + 1;
  _bits_per_clause   = log2(maxClId) + 1;

  _bits_of_data_size = log2(maxVarId + maxClId) + 1;

  _variable_mask = _clause_mask = _data_size_mask = 0;
  for (unsigned int i = 0; i < _bits_per_variable; i++)
    _variable_mask = (_variable_mask << 1) + 1;
  for (unsigned int i = 0; i < _bits_per_clause; i++)
    _clause_mask = (_clause_mask << 1) + 1;
  for (unsigned int i = 0; i < _bits_of_data_size; i++)
    _data_size_mask = (_data_size_mask << 1) + 1;
}