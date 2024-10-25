// Copyright (c) 2021-2024, David H. Hovemeyer <david.hovemeyer@gmail.com>
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
#include <algorithm>
#include <utility>
#include <map>
#include <unordered_set>
#include "grammar_symbols.h"
#include "parse.tab.h"
#include "node.h"
#include "ast.h"
#include "exceptions.h"
#include "semantic_analysis.h"

SemanticAnalysis::SemanticAnalysis(const Options &options)
  : m_options(options)
  , m_global_symtab(new SymbolTable(nullptr, "global")) {
  m_cur_symtab = m_global_symtab;
  m_all_symtabs.push_back(m_global_symtab);
}

SemanticAnalysis::~SemanticAnalysis() {
  // The semantic analyzer owns the SymbolTables and their Symbols,
  // so delete them. Note that the AST has pointers to Symbol objects,
  // so the SemanticAnalysis object should live at least as long
  // as the AST.
  for (auto i = m_all_symtabs.begin(); i != m_all_symtabs.end(); ++i)
    delete *i;
}

void SemanticAnalysis::visit_struct_type(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_union_type(Node *n) {
  RuntimeError::raise("union types aren't supported");
}

void SemanticAnalysis::visit_variable_declaration(Node *n) {
  // TODO: implement
}

// Helper function to convert token string to BasicTypeKind
BasicTypeKind SemanticAnalysis::string_to_basic_type_kind(const std::string &str) {
    if (str == "char") return BasicTypeKind::CHAR;
    if (str == "short") return BasicTypeKind::SHORT;
    if (str == "int") return BasicTypeKind::INT;
    if (str == "long") return BasicTypeKind::LONG;
    if (str == "void") return BasicTypeKind::VOID;
    throw std::runtime_error("Unknown basic type: " + str);
}

// Helper function to check if a string is a type qualifier
bool SemanticAnalysis::is_type_qualifier(const std::string &str) {
    return str == "const" || str == "volatile";
}

void SemanticAnalysis::visit_basic_type(Node *n) {
    assert(n != nullptr && "AST_BASIC_TYPE node is null.");

    std::unordered_set<std::string> specifiers;
    std::unordered_set<std::string> qualifiers;
    std::string modifier;  // signed or unsigned

    // Iterate over child nodes to extract specifiers, modifiers, and qualifiers
    for (unsigned i = 0; i < n->get_num_kids(); ++i) {
        Node *child = n->get_kid(i);
        std::string token = child->get_str();

        if (is_type_qualifier(token)) {
            qualifiers.insert(token);
        }
        else if (token == "signed" || token == "unsigned") {
            if (!modifier.empty() && modifier != token) {
                SemanticError::raise(n->get_loc(), "signed and unsigned cannot be used together.");
            }
            modifier = token;
        }
        else {
            // Assume it's a type specifier
            specifiers.insert(token);
        }
    }

    // Apply default rules
    if (specifiers.empty() || (!specifiers.count("char") && !specifiers.count("int") && !specifiers.count("void"))) {
        specifiers.insert("int");
    }

    // Validation rules
    if (specifiers.count("void") && specifiers.size() > 1) {
        SemanticError::raise(n->get_loc(), "Void type cannot be combined with other type specifiers.");
    }

    if (specifiers.count("long") && !specifiers.count("int")) {
        SemanticError::raise(n->get_loc(), "long can only be used with int.");
    }

    if (specifiers.count("short") && !specifiers.count("int")) {
        SemanticError::raise(n->get_loc(), "short can only be used with int.");
    }

    if (specifiers.count("long") && specifiers.count("short")) {
        SemanticError::raise(n->get_loc(), "long and short cannot be used together.");
    }

    // Determine signedness
    bool is_signed = (modifier != "unsigned");

    // Determine the BasicTypeKind
    BasicTypeKind basic_kind;
    if (specifiers.count("char")) {
        basic_kind = BasicTypeKind::CHAR;
    }
    else if (specifiers.count("void")) {
        basic_kind = BasicTypeKind::VOID;
    }
    else {
        if (specifiers.count("long")) {
            basic_kind = BasicTypeKind::LONG;
        } else if (specifiers.count("short")) {
            basic_kind = BasicTypeKind::SHORT;
        } else {
            basic_kind = BasicTypeKind::INT;
        }
    }

    // Create the base BasicType
    std::shared_ptr<Type> base_type = std::make_shared<BasicType>(basic_kind, is_signed);

    // Wrap the base type with qualifiers if any
    std::shared_ptr<Type> final_type = base_type;
    for (const auto &qual : qualifiers) {
        TypeQualifier tq = (qual == "const") ? TypeQualifier::CONST : TypeQualifier::VOLATILE;
        final_type = std::make_shared<QualifiedType>(final_type, tq);
    }

    // Annotate the AST node with the type
    n->set_type(final_type);
}

void SemanticAnalysis::visit_named_declarator(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_pointer_declarator(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_array_declarator(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_definition(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_declaration(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_parameter_list(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_parameter(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_statement_list(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_return_expression_statement(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_struct_type_definition(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_binary_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_unary_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_postfix_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_conditional_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_cast_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_call_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_field_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_indirect_field_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_array_element_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_variable_ref(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_literal_value(Node *n) {
  // TODO: implement
}

SymbolTable *SemanticAnalysis::enter_scope(const std::string &name) {
  SymbolTable *symtab = new SymbolTable(m_cur_symtab, name);
  m_all_symtabs.push_back(symtab);
  m_cur_symtab = symtab;
  return symtab;
}

void SemanticAnalysis::leave_scope() {
  assert(m_cur_symtab->get_parent() != nullptr);
  m_cur_symtab = m_cur_symtab->get_parent();
}

// TODO: implement helper functions
Node *SemanticAnalysis::promote_to_int(Node *n) {
  assert(n->get_type()->is_integral());
  assert(n->get_type()->get_basic_type_kind() < BasicTypeKind::INT);
  std::shared_ptr<Type> type =
    std::make_shared<BasicType>(BasicTypeKind::INT,
                                n->get_type()->is_signed());
  return implicit_conversion(n, type);
}

Node *SemanticAnalysis::implicit_conversion(Node *n,
                                            std::shared_ptr<Type> type) {
  std::unique_ptr<Node> conversion(
    new Node(AST_IMPLICIT_CONVERSION, {n}));
  conversion->set_type(type);
  return conversion.release();
}
