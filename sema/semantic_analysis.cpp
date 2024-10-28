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
    assert(n != nullptr);
    assert(n->get_tag() == AST_VARIABLE_DECLARATION);

    // Visit the base type to determine its type representation
    Node *base_type_node = n->get_kid(0);
    visit(base_type_node);
    std::shared_ptr<Type> base_type = base_type_node->get_type();
    assert(base_type);

    // The declarator list is the second child of the variable declaration node
    Node *declarator_list_node = n->get_kid(1);

    // Iterate over each declarator in the declarator list
    for (unsigned i = 0; i < declarator_list_node->get_num_kids(); ++i) {
        Node *declarator_node = declarator_list_node->get_kid(i);

        // Initialize member variables for the current declarator
        m_var_name.clear();
        m_var_type = base_type;

        // Visit the declarator to process its type and name
        visit(declarator_node);

        // Ensure that the variable name and type have been set
        assert(!m_var_name.empty());
        assert(m_var_type);

        // Check for redefinition in the current scope
        if (m_cur_symtab->has_symbol_local(m_var_name)) {
            SemanticError::raise(declarator_node->get_loc(),
                                 "Redefinition of variable '%s'", m_var_name.c_str());
        }

        // Prevent variables of type 'void' (unless it's a pointer to void)
        if (m_var_type->is_void() && !m_var_type->is_pointer()) {
            SemanticError::raise(declarator_node->get_loc(),
                                 "Variable '%s' declared as void", m_var_name.c_str());
        }

        // Add the variable to the symbol table
        Symbol *sym = m_cur_symtab->add_entry(
            declarator_node->get_loc(),
            SymbolKind::VARIABLE,
            m_var_name,
            m_var_type);

        // Annotate the declarator node with the symbol
        declarator_node->set_symbol(sym);
    }
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
    assert(n != nullptr);

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
    assert(n != nullptr);
    assert(n->get_tag() == AST_NAMED_DECLARATOR);

    // The identifier is the first child
    Node *ident_node = n->get_kid(0);
    m_var_name = ident_node->get_str();

    // Annotate the node with the type so far
    n->set_type(m_var_type);
}

void SemanticAnalysis::visit_pointer_declarator(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_POINTER_DECLARATOR);

    // Wrap the current type with a PointerType
    m_var_type = std::make_shared<PointerType>(m_var_type);

    // Process any type qualifiers (e.g., const, volatile)
    for (unsigned i = 0; i < n->get_num_kids() - 1; ++i) {
        Node *qualifier_node = n->get_kid(i);
        std::string qualifier = qualifier_node->get_str();
        TypeQualifier tq = (qualifier == "const") ? TypeQualifier::CONST : TypeQualifier::VOLATILE;
        m_var_type = std::make_shared<QualifiedType>(m_var_type, tq);
    }

    // Visit the child declarator
    Node *child_declarator = n->get_last_kid();
    visit(child_declarator);
}

void SemanticAnalysis::visit_array_declarator(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_ARRAY_DECLARATOR);

    // Visit the size expression (if any)
    Node *size_expr_node = n->get_kid(1);
    visit(size_expr_node);

    // Evaluate the size expression
    if (!size_expr_node->get_type()->is_integral()) {
        SemanticError::raise(size_expr_node->get_loc(),
                             "Array size must be an integer constant");
    }

    // Assume size is a literal integer for simplicity
    int size = 0;
    if (size_expr_node->get_tag() == AST_LITERAL_VALUE) {
        LiteralValue lv(size_expr_node->get_kid(0)->get_str());
        size = lv.get_int_value();
    } else {
        SemanticError::raise(size_expr_node->get_loc(),
                             "Array size must be an integer constant");
    }

    if (size <= 0) {
        SemanticError::raise(size_expr_node->get_loc(),
                             "Array size must be positive");
    }

    // Wrap the current type with an ArrayType
    m_var_type = std::make_shared<ArrayType>(m_var_type, size);

    // Visit the child declarator
    Node *child_declarator = n->get_kid(0);
    visit(child_declarator);
}

void SemanticAnalysis::visit_function_definition(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_FUNCTION_DEFINITION);

    // Get the return type
    Node *return_type_node = n->get_kid(0);
    visit(return_type_node);
    std::shared_ptr<Type> return_type = return_type_node->get_type();

    // Get the function name
    Node *ident_node = n->get_kid(1);
    std::string func_name = ident_node->get_str();

    // Get or create the function's symbol table
    Symbol *func_sym = m_global_symtab->lookup_local(func_name);
    SymbolTable *func_symtab;
    std::shared_ptr<Type> func_type;

    if (func_sym) {
        // Function already declared; check for consistency
        func_type = func_sym->get_type();
        if (!func_type->get_base_type()->is_same(return_type.get())) {
            SemanticError::raise(n->get_loc(), "Function '%s' return type mismatch", func_name.c_str());
        }
        func_symtab = func_sym->get_symtab();
        m_cur_symtab = func_symtab;
    } else {
        // Create function type and symbol table
        func_type = std::make_shared<FunctionType>(return_type);
        func_symtab = enter_scope("function " + func_name);
        m_cur_symtab->set_fn_type(func_type);
        func_sym = m_global_symtab->add_entry(
            ident_node->get_loc(),
            SymbolKind::FUNCTION,
            func_name,
            func_type);
    }

    // Process parameters
    Node *param_list_node = n->get_kid(2);
    visit(param_list_node);

    // Process function body
    Node *body_node = n->get_kid(3);
    visit(body_node);

    // Leave function scope
    leave_scope();
}


void SemanticAnalysis::visit_function_declaration(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_parameter_list(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_FUNCTION_PARAMETER_LIST);

    if (n->get_num_kids() == 0) {
        // Empty parameter list (void)
        return;
    }

    for (unsigned i = 0; i < n->get_num_kids(); ++i) {
        Node *param_node = n->get_kid(i);
        visit(param_node);
    }
}

void SemanticAnalysis::visit_function_parameter(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_FUNCTION_PARAMETER);

    // Process the parameter type
    Node *param_type_node = n->get_kid(0);
    visit(param_type_node);
    std::shared_ptr<Type> param_type = param_type_node->get_type();

    // Process the declarator
    Node *declarator_node = n->get_kid(1);
    m_var_name.clear();
    m_var_type = param_type;
    visit(declarator_node);

    // Add parameter to symbol table
    if (m_cur_symtab->has_symbol_local(m_var_name)) {
        SemanticError::raise(declarator_node->get_loc(), "Duplicate parameter '%s'", m_var_name.c_str());
    }

    Symbol *sym = m_cur_symtab->add_entry(
        declarator_node->get_loc(),
        SymbolKind::VARIABLE,
        m_var_name,
        m_var_type);

    // Add parameter to function type
    m_cur_symtab->get_fn_type()->add_member(Member(m_var_name, m_var_type));

    declarator_node->set_symbol(sym);
}

void SemanticAnalysis::visit_statement_list(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_STATEMENT_LIST);

    // Do not enter a new scope for function body
    bool is_function_body = m_cur_symtab->has_fn_type();

    if (!is_function_body) {
        std::string scope_name = "block " + std::to_string(n->get_loc().get_line());
        enter_scope(scope_name);
    }

    for (unsigned i = 0; i < n->get_num_kids(); ++i) {
        Node *stmt_node = n->get_kid(i);
        visit(stmt_node);
    }

    if (!is_function_body) {
        leave_scope();
    }
}

void SemanticAnalysis::visit_return_expression_statement(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_RETURN_EXPRESSION_STATEMENT);

    // Visit the expression
    Node *expr_node = n->get_kid(0);
    visit(expr_node);

    // Get the function's return type
    std::shared_ptr<Type> fn_return_type = m_cur_symtab->get_fn_type()->get_base_type();
    std::shared_ptr<Type> expr_type = expr_node->get_type();

    // Check type compatibility
    if (!expr_type->is_same(fn_return_type.get())) {
        SemanticError::raise(expr_node->get_loc(), "Return type mismatch");
    }

    n->set_type(fn_return_type);
}


void SemanticAnalysis::visit_struct_type_definition(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_binary_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_BINARY_EXPRESSION);

    Node *left_node = n->get_kid(0);
    Node *op_node = n->get_kid(1);
    Node *right_node = n->get_kid(2);

    visit(left_node);
    visit(right_node);

    std::string op_str = op_node->get_str();
    std::shared_ptr<Type> left_type = left_node->get_type();
    std::shared_ptr<Type> right_type = right_node->get_type();

    if (op_str == "=") {
        // Assignment
        if (!left_node->has_symbol()) {
            SemanticError::raise(left_node->get_loc(), "Left operand must be an lvalue");
        }
        if (!right_type->is_same(left_type.get())) {
            SemanticError::raise(n->get_loc(), "Type mismatch in assignment");
        }
        n->set_type(left_type);
    } else {
        // Other binary operations
        if (!left_type->is_integral() || !right_type->is_integral()) {
            SemanticError::raise(n->get_loc(), "Operands must be integral types");
        }
        n->set_type(left_type); // Simplification
    }
}

void SemanticAnalysis::visit_unary_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_UNARY_EXPRESSION);

    Node *op_node = n->get_kid(0);
    Node *expr_node = n->get_kid(1);

    visit(expr_node); // This will now handle AST_LITERAL_VALUE nodes
    std::shared_ptr<Type> expr_type = expr_node->get_type();
    std::string op_str = op_node->get_str();

    if (op_str == "-") {
        if (!expr_type->is_integral()) {
            SemanticError::raise(expr_node->get_loc(), "Operand must be integral");
        }
        n->set_type(expr_type);
    } else {
        SemanticError::raise(n->get_loc(), "Unsupported unary operator '%s'", op_str.c_str());
    }
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
    assert(n != nullptr);
    assert(n->get_tag() == AST_VARIABLE_REF);

    Node *ident_node = n->get_kid(0);
    std::string var_name = ident_node->get_str();

    Symbol *sym = m_cur_symtab->lookup_recursive(var_name);
    if (!sym) {
        SemanticError::raise(ident_node->get_loc(), "Undefined variable '%s'", var_name.c_str());
    }

    n->set_symbol(sym);
    n->set_type(sym->get_type());
}

void SemanticAnalysis::visit_literal_value(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_LITERAL_VALUE);

    Node *tok_node = n->get_kid(0);
    int tok_tag = tok_node->get_tag();
    std::string tok_str = tok_node->get_str();
    std::shared_ptr<Type> lit_type;

    if (tok_tag == TOK_INT_LIT) {
        // Integer literal
        lit_type = std::make_shared<BasicType>(BasicTypeKind::INT, true);
    } else if (tok_tag == TOK_CHAR_LIT) {
        // Character literal
        lit_type = std::make_shared<BasicType>(BasicTypeKind::CHAR, true);
    } else if (tok_tag == TOK_STR_LIT) {
        // String literal (array of char)
        lit_type = std::make_shared<ArrayType>(
            std::make_shared<BasicType>(BasicTypeKind::CHAR, true),
            tok_str.size());
    } else {
        SemanticError::raise(n->get_loc(), "Unknown literal");
    }

    n->set_type(lit_type);
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
                                            std::shared_ptr<Type> &type) {
  std::unique_ptr<Node> conversion(
    new Node(AST_IMPLICIT_CONVERSION, {n}));
  conversion->set_type(type);
  return conversion.release();
}
