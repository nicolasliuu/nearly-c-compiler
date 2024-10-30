// Copyright (c) 2021-2023, David H. Hovemeyer <david.hovemeyer@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.

#include <cassert>
#include "node_base.h"

NodeBase::NodeBase()
  // TODO: initialize member variables (e.g., pointer to Symbol)
  : m_symbol(nullptr), m_type(nullptr)
{
}

NodeBase::~NodeBase() {
}

// TODO: implement member functions
// Sets the symbol table entry for this node
void NodeBase::set_symbol(Symbol *symbol) {
  m_symbol = symbol;
}

// Sets the type for this node
void NodeBase::set_type(const std::shared_ptr<Type> type) {
  m_type = type;
}

// Checks if this node has an associated symbol
bool NodeBase::has_symbol() const {
  return m_symbol != nullptr;
}

// Retrieves the associated symbol
Symbol *NodeBase::get_symbol() const {
  return m_symbol;
}

// Retrieves the type associated with this node
std::shared_ptr<Type> NodeBase::get_type() const {
  assert(m_type && "Type not set for this node.");
  return m_type;
}
