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
#include <iostream>
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
    assert(n != nullptr);
    assert(n->get_tag() == AST_STRUCT_TYPE);

    // Extract the struct name
    Node *name_node = n->get_kid(0);
    std::string struct_name = name_node->get_str();

    // Form the symbol name with "struct " prefix
    std::string symbol_name = "struct " + struct_name;

    // Look up the struct type in the current and parent symbol tables
    Symbol *struct_sym = m_cur_symtab->lookup_recursive(symbol_name);
    if (!struct_sym) {
        SemanticError::raise(n->get_loc(), "Undefined struct type '%s'", struct_name.c_str());
    }

    // Ensure the symbol is of kind TYPE and is a StructType
    if (struct_sym->get_kind() != SymbolKind::TYPE) {
        SemanticError::raise(n->get_loc(), "'%s' is not a struct type", struct_name.c_str());
    }

    std::shared_ptr<Type> struct_type = struct_sym->get_type();
    if (!struct_type->is_struct()) {
        SemanticError::raise(n->get_loc(), "'%s' is not a struct type", struct_name.c_str());
    }

    // Annotate the node with the struct type
    n->set_type(struct_type);
}


void SemanticAnalysis::visit_union_type(Node *n) {
  RuntimeError::raise("union types aren't supported");
}

void SemanticAnalysis::visit_variable_declaration(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_VARIABLE_DECLARATION);

    // Access the base type node
    Node *base_type_node = n->get_kid(1);
    visit(base_type_node);
    std::shared_ptr<Type> base_type = base_type_node->get_type();
    assert(base_type);

    // Access the declarator list node
    Node *declarator_list_node = n->get_kid(2);

    // Iterate over each declarator in the declarator list
    for (unsigned i = 0; i < declarator_list_node->get_num_kids(); ++i) {
        Node *declarator_node = declarator_list_node->get_kid(i);

        // Initialize member variables for the current declarator
        m_var_name.clear();
        m_var_type = base_type;

        // Visit the declarator to process its name and type
        visit(declarator_node);

        // Add the symbol to the current symbol table
        if (m_cur_symtab->has_symbol_local(m_var_name)) {
            SemanticError::raise(declarator_node->get_loc(), "Duplicate variable '%s'", m_var_name.c_str());
        }

        Symbol *sym = m_cur_symtab->add_entry(
            declarator_node->get_loc(),
            SymbolKind::VARIABLE,
            m_var_name,
            m_var_type
        );

        // Annotate the declarator node with the symbol and type
        declarator_node->set_symbol(sym);
        declarator_node->set_type(m_var_type);
    }

    // Set the type on the AST_VARIABLE_DECLARATION node
    n->set_type(base_type);
}

// Helper function to convert token string to BasicTypeKind
// BasicTypeKind SemanticAnalysis::string_to_basic_type_kind(const std::string &str) {
//     if (str == "char") return BasicTypeKind::CHAR;
//     if (str == "short") return BasicTypeKind::SHORT;
//     if (str == "int") return BasicTypeKind::INT;
//     if (str == "long") return BasicTypeKind::LONG;
//     if (str == "void") return BasicTypeKind::VOID;
//     throw std::runtime_error("Unknown basic type: " + str);
// }

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

    // Existing validation: void cannot be combined with other specifiers
    if (specifiers.count("void") && specifiers.size() > 1) {
        SemanticError::raise(n->get_loc(), "Void type cannot be combined with other type specifiers.");
    }

    // **New Validation: void cannot have qualifiers**
    if (specifiers.count("void") && !qualifiers.empty()) {
        SemanticError::raise(n->get_loc(), "Type qualifiers 'const' and 'volatile' cannot be applied to 'void'.");
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
    if (!final_type) {
        std::cerr << "Error: final_type is nullptr in visit_basic_type\n";
    } 
    n->set_type(final_type);
}

void SemanticAnalysis::visit_named_declarator(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_NAMED_DECLARATOR);

    // Ensure that the named declarator has at least one child (the identifier)
    if (n->get_num_kids() < 1) {
        SemanticError::raise(n->get_loc(), "AST_NAMED_DECLARATOR node has no children.");
    }

    // The identifier is always the last child
    Node *ident_node = n->get_kid(n->get_num_kids() - 1);

    // Validate the identifier node
    if (ident_node == nullptr || ident_node->get_str().empty()) {
        SemanticError::raise(n->get_loc(), "Identifier in AST_NAMED_DECLARATOR is missing or empty.");
    }

    // Set the member variable m_var_name
    m_var_name = ident_node->get_str();

    // Let higher-level visitors handle symbol table additions.
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

    // Visit the child declarator first to get its type
    Node *child_declarator = n->get_kid(0);
    visit(child_declarator);

    // Retrieve the child declarator's type
    std::shared_ptr<Type> child_type = child_declarator->get_type();
    if (!child_type) {
        SemanticError::raise(child_declarator->get_loc(), "Child declarator type not set");
    }

    // Visit the size expression (if any)
    Node *size_expr_node = n->get_kid(1);
    if (size_expr_node->get_num_kids() > 0) { // Assuming size expression exists
        visit(size_expr_node);
        // Ensure size is a constant integer
        std::shared_ptr<Type> size_type = size_expr_node->get_type();
        if (!size_type->is_integral()) {
            SemanticError::raise(size_expr_node->get_loc(),
                                 "Array size must be an integer constant");
        }

        // Assume size is a literal integer for simplicity
        int size = 0;
        if (size_expr_node->get_tag() == AST_LITERAL_VALUE) {
            Node *lit_node = size_expr_node->get_kid(0);
            if (lit_node->get_tag() == TOK_INT_LIT) {
                size = std::stoi(lit_node->get_str());
            } else {
                SemanticError::raise(size_expr_node->get_loc(),
                                     "Array size must be an integer literal");
            }
        } else {
            SemanticError::raise(size_expr_node->get_loc(),
                                 "Array size must be an integer constant");
        }

        if (size <= 0) {
            SemanticError::raise(size_expr_node->get_loc(),
                                 "Array size must be positive");
        }

        // Wrap the child type with an ArrayType
        std::shared_ptr<Type> array_type = std::make_shared<ArrayType>(child_type, size);

        // Set the type on this array declarator node
        n->set_type(array_type);
    } else {
        SemanticError::raise(n->get_loc(), "Array declarator missing size expression");
    }
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
    assert(n != nullptr);
    assert(n->get_tag() == AST_FUNCTION_DECLARATION);

    // Extract return type, function name, and parameter list
    Node *return_type_node = n->get_kid(0);
    Node *name_node = n->get_kid(1);
    Node *param_list_node = n->get_kid(2);

    // Visit the return type to determine the function's return type
    visit(return_type_node);
    std::shared_ptr<Type> return_type = return_type_node->get_type();

    // Extract function name
    std::string func_name = name_node->get_str();

    // Form the symbol name
    std::string symbol_name = func_name;

    // Check if the function is already declared or defined
    Symbol *existing_func = m_cur_symtab->lookup_local(symbol_name);
    if (existing_func) {
        // Ensure the existing declaration matches the new one
        std::shared_ptr<Type> existing_type = existing_func->get_type();
        if (!existing_type->is_same(return_type.get())) {
            SemanticError::raise(n->get_loc(), "Function declaration error: return type mismatch for function '%s'", func_name.c_str());
        }

        // Further checks on parameters can be added here (e.g., parameter count and types)
    } else {
        // Declare the function with its return type
        std::shared_ptr<FunctionType> func_type = std::make_shared<FunctionType>(return_type);
        m_cur_symtab->add_entry(n->get_loc(), SymbolKind::FUNCTION, func_name, func_type);
        existing_func = m_cur_symtab->lookup_local(symbol_name);
    }

    // Enter the function's symbol table scope
    SymbolTable *func_symtab = enter_scope("function " + func_name);
    m_cur_symtab->set_fn_type(existing_func->get_type());

    // Visit the parameter list
    visit(param_list_node);

    // Leave the function's symbol table scope
    leave_scope();
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
    m_var_name.clear();          // Clear previous variable name
    m_var_type = param_type;     // Set the current variable type
    visit(declarator_node);      // This sets m_var_name and m_var_type

    // Ensure that m_var_name has been set
    if (m_var_name.empty()) {
        SemanticError::raise(declarator_node->get_loc(), "Function parameter declarator missing name.");
    }

    // Add parameter to symbol table
    if (m_cur_symtab->has_symbol_local(m_var_name)) {
        SemanticError::raise(declarator_node->get_loc(), "Duplicate parameter '%s'", m_var_name.c_str());
    }

    Symbol *sym = m_cur_symtab->add_entry(
        declarator_node->get_loc(),
        SymbolKind::VARIABLE,
        m_var_name,
        m_var_type
    );

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
    assert(n != nullptr);
    assert(n->get_tag() == AST_STRUCT_TYPE_DEFINITION);

    // Extract the struct name
    Node *name_node = n->get_kid(0);
    std::string struct_name = name_node->get_str();

    // Form the symbol name with "struct " prefix
    std::string symbol_name = "struct " + struct_name;

    // Check if the struct is already defined in the current scope
    if (m_cur_symtab->lookup_local(symbol_name)) {
        SemanticError::raise(n->get_loc(), "struct type definition error: struct '%s' is already defined", struct_name.c_str());
    }

    // Create a new StructType instance
    std::shared_ptr<StructType> struct_type = std::make_shared<StructType>(struct_name);

    // Add the struct type to the current symbol table
    m_cur_symtab->add_entry(n->get_loc(), SymbolKind::TYPE, symbol_name, struct_type);

    // Enter a new scope for the struct members
    enter_scope("struct " + struct_name);

    // Visit all member declarations within the struct
    Node *member_list_node = n->get_kid(1); // Assuming the second child is the member list
    visit(member_list_node);

    // Add members to the StructType
    for (const auto &symbol : m_cur_symtab->get_symbols()) {
        struct_type->add_member(Member(symbol->get_name(), symbol->get_type()));
    }

    // Leave the struct member scope
    leave_scope();

    // Annotate the node with the struct type
    n->set_type(struct_type);
}

void SemanticAnalysis::visit_binary_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_BINARY_EXPRESSION);

    int op_tag = n->get_kid(0)->get_tag(); // Operator token

    Node *left_node = n->get_kid(1);
    Node *right_node = n->get_kid(2);

    // Visit operands
    visit(left_node);
    visit(right_node);

    // Get types of operands
    std::shared_ptr<Type> left_type = left_node->get_type();
    std::shared_ptr<Type> right_type = right_node->get_type();

    // Check if operands are integral or pointer types
    bool left_is_integral = left_type->is_integral();
    bool right_is_integral = right_type->is_integral();
    bool left_is_pointer = left_type->is_pointer();
    bool right_is_pointer = right_type->is_pointer();

    if (op_tag == TOK_ASSIGN) {
        // Assignment operator '='

        // Left operand must be an lvalue
        int l_tag = left_node->get_tag();
        if (l_tag == AST_LITERAL_VALUE || l_tag == AST_FUNCTION_CALL_EXPRESSION) { 
            SemanticError::raise(n->get_loc(), "Binary expression error: Left operand must be an lvalue");
        }

        // Left operand must not be const-qualified
        if (left_type->is_const()) {
            SemanticError::raise(n->get_loc(), "Cannot assign to a const-qualified type");
        }

        // Check type compatibility for assignment
        if (!types_compatible_for_assignment(left_type, right_type)) {
            SemanticError::raise(n->get_loc(), "Type mismatch in assignment");
        }

        // Insert implicit conversion if needed
        if (!left_type->is_same(right_type.get())) {
            // Perform implicit conversion of right operand to left type
            Node *converted_right = implicit_conversion(right_node, left_type);
            n->set_kid(2, converted_right);
            right_node = converted_right;
        }

        // The type of the assignment expression is the type of the left operand
        n->set_type(left_type);

    } else if (op_tag == TOK_PLUS || op_tag == TOK_MINUS) {
        // Addition '+' or subtraction '-'

        if ((left_is_pointer && right_is_integral) ||
            (left_is_integral && right_is_pointer && op_tag == TOK_PLUS)) {
            // Pointer arithmetic: pointer +/- integer or integer + pointer

            if (left_is_integral && right_is_pointer && op_tag == TOK_PLUS) {
                // Swap operands to have pointer on the left
                std::swap(left_node, right_node);
                std::swap(left_type, right_type);
                left_is_integral = left_type->is_integral();
                left_is_pointer = left_type->is_pointer();
                right_is_integral = right_type->is_integral();
                right_is_pointer = right_type->is_pointer();
            }

            // Promote integer operand if less precise than int
            if (determine_precision(right_type.get(), right_node->get_loc()) < determine_precision(get_int_type().get(), right_node->get_loc())) {
                Node *promoted_right = promote_to_int(right_node);
                n->set_kid(2, promoted_right);
                right_node = promoted_right;
                right_type = right_node->get_type();
            }

            // The result type is the type of the pointer
            n->set_type(left_type);

        } else if (left_is_integral && right_is_integral) {
            // Integer addition or subtraction

            // Apply usual arithmetic conversions
            is_less_precise(left_node, right_node, n);

            // The result type is already set by is_less_precise

        } else if (op_tag == TOK_MINUS && left_is_pointer && right_is_pointer) {
            // Pointer subtraction

            // Both pointers must have the same unqualified base type
            const Type *left_base_unqual = left_type->get_base_type()->get_unqualified_type();
            const Type *right_base_unqual = right_type->get_base_type()->get_unqualified_type();

            if (!left_base_unqual->is_same(right_base_unqual)) {
                SemanticError::raise(n->get_loc(), "Invalid operands to binary '-' (pointers to different types)");
            }

            // The result is of type ptrdiff_t
            n->set_type(get_ptrdiff_t_type());

        } else {
            SemanticError::raise(n->get_loc(), "Invalid operands to binary '+' or '-'");
        }

    } else if (op_tag == TOK_ASTERISK || op_tag == TOK_DIVIDE || op_tag == TOK_MOD) {
        // Multiplication '*', division '/', or modulus '%'

        if (left_is_integral && right_is_integral) {
            // Apply usual arithmetic conversions
            is_less_precise(left_node, right_node, n);

            // Check that operands are not pointers
            if (left_is_pointer || right_is_pointer) {
                SemanticError::raise(n->get_loc(), "Cannot perform arithmetic on pointer types with these operators");
            }

            // The result type is already set by is_less_precise

        } else {
            SemanticError::raise(n->get_loc(), "Invalid operands to binary operator");
        }

    } else if (op_tag == TOK_LOGICAL_AND || op_tag == TOK_LOGICAL_OR) {
        // Logical AND '&&' or OR '||'

        if (left_type->is_void() || right_type->is_void()) {
            SemanticError::raise(n->get_loc(), "Operands must not be of void type");
        }

        if (left_type->is_array() || left_type->is_struct() ||
            right_type->is_array() || right_type->is_struct()) {
            SemanticError::raise(n->get_loc(), "Operands must not be struct or array types");
        }

        // The result type is int
        n->set_type(get_int_type());

    } else if (op_tag == TOK_EQUALITY || op_tag == TOK_INEQUALITY) {
        // Equality '==' or inequality '!='

        if ((left_is_integral && right_is_integral) || (left_is_pointer && right_is_pointer)) {

            if (left_is_integral && right_is_integral) {
                // Apply usual arithmetic conversions
                is_less_precise(left_node, right_node, n);
            } else if (left_is_pointer && right_is_pointer) {
                // Pointers must have compatible types
                const Type *left_base_unqual = left_type->get_base_type()->get_unqualified_type();
                const Type *right_base_unqual = right_type->get_base_type()->get_unqualified_type();

                if (!left_base_unqual->is_same(right_base_unqual)) {
                    SemanticError::raise(n->get_loc(), "Invalid operands to equality operator (pointers to different types)");
                }
            }

            // The result type is int
            n->set_type(get_int_type());

        } else {
            SemanticError::raise(n->get_loc(), "Invalid operands to equality operator");
        }

    } else if (op_tag == TOK_LT || op_tag == TOK_LTE || op_tag == TOK_GT || op_tag == TOK_GTE) {
        // Relational operators '<', '<=', '>', '>='

        if ((left_is_integral && right_is_integral) || (left_is_pointer && right_is_pointer)) {

            if (left_is_integral && right_is_integral) {
                // Apply usual arithmetic conversions
                is_less_precise(left_node, right_node, n);
            } else if (left_is_pointer && right_is_pointer) {
                // Pointers must have compatible types
                const Type *left_base_unqual = left_type->get_base_type()->get_unqualified_type();
                const Type *right_base_unqual = right_type->get_base_type()->get_unqualified_type();

                if (!left_base_unqual->is_same(right_base_unqual)) {
                    SemanticError::raise(n->get_loc(), "Invalid operands to relational operator (pointers to different types)");
                }
            }

            // The result type is int
            n->set_type(get_int_type());

        } else {
            SemanticError::raise(n->get_loc(), "Invalid operands to relational operator");
        }

    } else {
        SemanticError::raise(n->get_loc(), "Unsupported binary operator");
    }
}

void SemanticAnalysis::visit_unary_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_UNARY_EXPRESSION);

    // Retrieve the operator and operand nodes
    Node *op_node = n->get_kid(0);
    Node *expr_node = n->get_kid(1);

    // Visit the operand to perform semantic analysis
    visit(expr_node);
    std::shared_ptr<Type> expr_type = expr_node->get_type();

    // Get the operator token tag
    int op_tag = op_node->get_tag();

    // Handle different unary operators based on the operator token
    switch (op_tag) {
        case TOK_AMPERSAND: { // Address-of operator '&'
            // The operand must be an l-value
            bool is_lvalue = false;
            switch (expr_node->get_tag()) {
                case AST_VARIABLE_REF:
                case AST_POSTFIX_EXPRESSION:
                    is_lvalue = true;
                    break;
                default:
                    is_lvalue = false;
            }

            if (!is_lvalue) {
                SemanticError::raise(n->get_loc(),
                                     "Operand of '&' must be an lvalue");
            }

            // The operand cannot be a literal value
            if (expr_node->get_tag() == AST_LITERAL_VALUE) {
                SemanticError::raise(n->get_loc(),
                                     "Cannot take the address of a literal value");
            }

            // Set the type to be a pointer to the operand's type
            std::shared_ptr<Type> ptr_type = std::make_shared<PointerType>(expr_type);
            n->set_type(ptr_type);
            break;
        }

        case TOK_ASTERISK: { // Dereference operator '*'
            // The operand must be a pointer type
            if (!expr_type->is_pointer()) {
                SemanticError::raise(n->get_loc(),
                                     "Cannot dereference a non-pointer type with '*'");
            }

            // Retrieve the base type (pointee type) using get_base_type()
            std::shared_ptr<Type> base_type = expr_type->get_base_type();
            if (!base_type) {
                SemanticError::raise(n->get_loc(),
                                     "Pointer type does not have a base type");
            }

            // Set the type to the base type pointed to by the operand
            n->set_type(base_type);
            break;
        }

        case TOK_NOT: // Logical NOT '!'
        case TOK_MINUS: // Unary minus '-'
        case TOK_BITWISE_COMPL: { // Bitwise complement '~'
            // Unary operators that require integral operands

            // Check if the operand is an integral type
            if (!expr_type->is_integral()) {
                SemanticError::raise(n->get_loc(),
                                     "Unary operator '%s' requires an integral operand",
                                     op_node->get_str().c_str());
            }

            // Handle type promotion for literal values
            if (expr_node->get_tag() == AST_LITERAL_VALUE) {
                // Promote literal values to INT if necessary
                std::shared_ptr<Type> promoted_type = std::make_shared<BasicType>(BasicTypeKind::INT, true);
                n->set_type(promoted_type);
            }
            else if (expr_node->get_tag() == AST_VARIABLE_REF ||
                     expr_node->get_tag() == AST_POSTFIX_EXPRESSION) {
                // For variable references and expressions that are l-values, set the type accordingly
                n->set_type(expr_type);
            }
            else {
                // Unsupported operand type for the unary operator
                SemanticError::raise(n->get_loc(),
                                     "Unary operator '%s' cannot be applied to this operand",
                                     op_node->get_str().c_str());
            }
            break;
        }

        default:
            // Unsupported unary operator
            SemanticError::raise(n->get_loc(),
                                 "Unsupported unary operator '%s'",
                                 op_node->get_str().c_str());
    }
}

void SemanticAnalysis::visit_postfix_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_POSTFIX_EXPRESSION);

    // The first child is the primary expression
    Node *primary_expr = n->get_kid(0);
    visit(primary_expr);
    std::shared_ptr<Type> primary_type = primary_expr->get_type();

    // The second child determines the postfix operation
    Node *postfix_op = n->get_kid(1);

    if (postfix_op->get_tag() == TOK_LBRACKET) {
        // Array Subscript: a[i]
        Node *index_expr = n->get_kid(2);
        visit(index_expr);
        std::shared_ptr<Type> index_type = index_expr->get_type();

        // Check that primary expression is a pointer or array
        if (!primary_type->is_pointer() && !primary_type->is_array()) {
            SemanticError::raise(n->get_loc(), "Type '%s' is not an array or pointer for indexing",
                                 primary_type->as_str().c_str());
        }

        // Check that index is of integral type
        if (!index_type->is_integral()) {
            SemanticError::raise(index_expr->get_loc(), "Array index must be an integer type");
        }

        // The result type is the type pointed to by the primary expression
        std::shared_ptr<Type> element_type;
        if (primary_type->is_array()) {
            element_type = primary_type->get_base_type();
        } else { // pointer
            element_type = primary_type->get_base_type();
        }

        n->set_type(element_type);
    }
    else if (postfix_op->get_tag() == TOK_DOT || postfix_op->get_tag() == TOK_ARROW) {
        // Struct Member Access: obj.field or obj->field
        Node *member_node = n->get_kid(2);
        std::string member_name = member_node->get_str();

        // Determine if it's direct or indirect access
        bool is_indirect = (postfix_op->get_tag() == TOK_ARROW);

        // If indirect, primary expression must be a pointer to struct
        if (is_indirect) {
            if (!primary_type->is_pointer()) {
                SemanticError::raise(n->get_loc(), "Type '%s' is not a pointer for '->' operator",
                                     primary_type->as_str().c_str());
            }
            std::shared_ptr<Type> pointee_type = primary_type->get_base_type();
            if (!pointee_type->is_struct()) {
                SemanticError::raise(n->get_loc(), "Type '%s' is not a struct for '->' operator",
                                     pointee_type->as_str().c_str());
            }
            primary_type = pointee_type;
        } else {
            if (!primary_type->is_struct()) {
                SemanticError::raise(n->get_loc(), "Type '%s' is not a struct for '.' operator",
                                     primary_type->as_str().c_str());
            }
        }

        // Retrieve the StructType
        StructType *struct_type = dynamic_cast<StructType*>(primary_type.get());
        if (!struct_type) {
            SemanticError::raise(n->get_loc(), "Invalid struct type '%s'",
                                 primary_type->as_str().c_str());
        }

        // Lookup the member in the struct
        const Member *member = struct_type->find_member(member_name);
        if (!member) {
            SemanticError::raise(n->get_loc(), "Struct '%s' has no member named '%s'",
                                 struct_type->get_name().c_str(), member_name.c_str());
        }

        // Set the type of the postfix expression to the member's type
        n->set_type(member->get_type());
    }
    else {
        SemanticError::raise(n->get_loc(), "Unsupported postfix operation");
    }
}

void SemanticAnalysis::visit_conditional_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_cast_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_CAST_EXPRESSION);

    // Children: type_to_cast_to, expression_to_cast
    Node *type_node = n->get_kid(0);
    Node *expr_node = n->get_kid(1);

    // Visit the type node to determine the target type
    visit(type_node);
    std::shared_ptr<Type> target_type = type_node->get_type();

    // Visit the expression to be cast
    visit(expr_node);
    std::shared_ptr<Type> expr_type = expr_node->get_type();

    // Validate the cast: In C, most casts are allowed, but some restrictions apply
    // For simplicity, we'll allow any cast between scalar types and pointers
    bool valid_cast = false;

    if (target_type->is_integral() && expr_type->is_integral()) {
        valid_cast = true;
    }
    else if (target_type->is_pointer() && expr_type->is_pointer()) {
        valid_cast = true;
    }
    else if (target_type->is_pointer() && expr_type->is_integral()) {
        // Casting integer to pointer is implementation-defined, but allowed
        valid_cast = true;
    }
    else if (target_type->is_integral() && expr_type->is_pointer()) {
        // Casting pointer to integer is implementation-defined, but allowed
        valid_cast = true;
    }

    if (!valid_cast) {
        SemanticError::raise(n->get_loc(), "Invalid cast from '%s' to '%s'",
                             expr_type->as_str().c_str(),
                             target_type->as_str().c_str());
    }

    // Set the type of the cast expression to the target type
    n->set_type(target_type);

    // Insert the cast node
    n->set_kid(1, implicit_conversion(expr_node, target_type));
}


void SemanticAnalysis::visit_function_call_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_FUNCTION_CALL_EXPRESSION);

    // Children: function_name_node, argument_list_node
    Node *func_name_node = n->get_kid(0);
    Node *arg_list_node = n->get_kid(1);

    // Visit the function name node (could be a variable reference)
    visit(func_name_node);
    std::shared_ptr<Type> func_type = func_name_node->get_type();

    // Ensure that func_type is a function type
    if (!func_type->is_function()) {
        SemanticError::raise(func_name_node->get_loc(), "Attempting to call a non-function type '%s'",
                             func_type->as_str().c_str());
    }

    // Retrieve the FunctionType
    FunctionType *function_type = dynamic_cast<FunctionType*>(func_type.get());
    if (!function_type) {
        SemanticError::raise(func_name_node->get_loc(), "Invalid function type for '%s'",
                             func_type->as_str().c_str());
    }

    // Visit each argument and collect their types
    std::vector<std::shared_ptr<Type>> arg_types;
    std::vector<Node*> args;
    for (unsigned i = 0; i < arg_list_node->get_num_kids(); ++i) {
        Node *arg_node = arg_list_node->get_kid(i);
        visit(arg_node);
        arg_types.push_back(arg_node->get_type());
        args.push_back(arg_node);
    }

    // Check the number of arguments
    size_t expected_args = function_type->get_num_members();
    size_t provided_args = arg_types.size();
    if (expected_args != provided_args) {
        SemanticError::raise(n->get_loc(), "Function '%s' expects %zu arguments but %zu were given",
                             func_type->as_str().c_str(), expected_args, provided_args);
    }

    // Check each argument's type compatibility
    for (size_t i = 0; i < expected_args; ++i) {
        std::shared_ptr<Type> param_type = function_type->get_member(i).get_type();
        std::shared_ptr<Type> arg_type = arg_types[i];

        if (!types_compatible_for_assignment(param_type, arg_type)) {
            SemanticError::raise(args[i]->get_loc(), "Type mismatch for argument %zu in function call", i + 1);
        }

        // Insert implicit conversion if necessary
        if (!param_type->is_same(arg_type.get())) {
            Node *converted_arg = implicit_conversion(args[i], param_type);
            arg_list_node->set_kid(i, converted_arg);
        }
    }

    // Set the type of the function call expression to the function's return type
    std::shared_ptr<Type> return_type = function_type->get_base_type();
    n->set_type(return_type);
}

void SemanticAnalysis::visit_field_ref_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_FIELD_REF_EXPRESSION);

    // Children: struct_expr_node, field_name_node
    Node *struct_expr_node = n->get_kid(0);
    Node *field_name_node = n->get_kid(1);
    std::string field_name = field_name_node->get_str();

    // Visit the struct expression
    visit(struct_expr_node);
    std::shared_ptr<Type> struct_type = struct_expr_node->get_type();

    // Ensure the struct expression is of struct type
    if (!struct_type->is_struct()) {
        SemanticError::raise(struct_expr_node->get_loc(), "Type '%s' is not a struct type for member access",
                             struct_type->as_str().c_str());
    }

    // Retrieve the StructType
    StructType *s_type = dynamic_cast<StructType*>(struct_type.get());
    if (!s_type) {
        SemanticError::raise(n->get_loc(), "Invalid struct type '%s'",
                             struct_type->as_str().c_str());
    }

    // Lookup the member in the struct
    const Member *member = s_type->find_member(field_name);
    if (!member) {
        SemanticError::raise(n->get_loc(), "Struct '%s' has no member named '%s'",
                             s_type->get_name().c_str(), field_name.c_str());
    }

    // Set the type of the field reference expression to the member's type
    n->set_type(member->get_type());
}

void SemanticAnalysis::visit_indirect_field_ref_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_INDIRECT_FIELD_REF_EXPRESSION);

    // Children: pointer_expr_node, field_name_node
    Node *pointer_expr_node = n->get_kid(0);
    Node *field_name_node = n->get_kid(1);
    std::string field_name = field_name_node->get_str();

    // Visit the pointer expression
    visit(pointer_expr_node);
    std::shared_ptr<Type> pointer_type = pointer_expr_node->get_type();

    // Ensure the pointer expression is a pointer to a struct
    if (!pointer_type->is_pointer()) {
        SemanticError::raise(pointer_expr_node->get_loc(), "Type '%s' is not a pointer for '->' operator",
                             pointer_type->as_str().c_str());
    }

    std::shared_ptr<Type> pointee_type = pointer_type->get_base_type();
    if (!pointee_type->is_struct()) {
        SemanticError::raise(pointer_expr_node->get_loc(), "Type '%s' is not a struct for '->' operator",
                             pointee_type->as_str().c_str());
    }

    // Retrieve the StructType
    StructType *s_type = dynamic_cast<StructType*>(pointee_type.get());
    if (!s_type) {
        SemanticError::raise(n->get_loc(), "Invalid struct type '%s'",
                             pointee_type->as_str().c_str());
    }

    // Lookup the member in the struct
    const Member *member = s_type->find_member(field_name);
    if (!member) {
        SemanticError::raise(n->get_loc(), "Struct '%s' has no member named '%s'",
                             s_type->get_name().c_str(), field_name.c_str());
    }

    // Set the type of the indirect field reference expression to the member's type
    n->set_type(member->get_type());
}


void SemanticAnalysis::visit_array_element_ref_expression(Node *n) {
    assert(n != nullptr);
    assert(n->get_tag() == AST_ARRAY_ELEMENT_REF_EXPRESSION);

    // Children: array_expr_node, index_expr_node
    Node *array_expr_node = n->get_kid(0);
    Node *index_expr_node = n->get_kid(1);

    // Visit the array expression
    visit(array_expr_node);
    std::shared_ptr<Type> array_type = array_expr_node->get_type();

    // Visit the index expression
    visit(index_expr_node);
    std::shared_ptr<Type> index_type = index_expr_node->get_type();

    // Check that the array expression is of array or pointer type
    if (!array_type->is_array() && !array_type->is_pointer()) {
        SemanticError::raise(array_expr_node->get_loc(), "Type '%s' is not an array or pointer for indexing",
                             array_type->as_str().c_str());
    }

    // Check that the index is of integral type
    if (!index_type->is_integral()) {
        SemanticError::raise(index_expr_node->get_loc(), "Array index must be of an integral type");
    }

    // Determine the element type
    std::shared_ptr<Type> element_type;
    if (array_type->is_array()) {
        element_type = array_type->get_base_type();
    } else { // pointer
        element_type = array_type->get_base_type();
    }

    // Set the type of the array element reference expression
    n->set_type(element_type);
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
        // String literal treated as pointer to char for assignments
        lit_type = std::make_shared<PointerType>(
            std::make_shared<BasicType>(BasicTypeKind::CHAR, true));
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

// Helper functions
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

bool SemanticAnalysis::types_compatible_for_assignment(const std::shared_ptr<Type> lhs, const std::shared_ptr<Type> rhs) {
    if (lhs->is_integral() && rhs->is_integral()) {
        // Integral types are compatible for assignment
        return true;
    }
    if (lhs->is_pointer() && rhs->is_pointer()) {
        // Check if base types are compatible
        const Type *lhs_base = lhs->get_base_type()->get_unqualified_type();
        const Type *rhs_base = rhs->get_base_type()->get_unqualified_type();
        return lhs_base->is_same(rhs_base);
    }
    if (lhs->is_struct() && rhs->is_struct()) {
        // Structs must be the same type
        return lhs->is_same(rhs.get());
    }
    // Other combinations are not compatible
    return false;
}

int SemanticAnalysis::determine_precision(const Type* type, const Location& loc) {
    if (type->is_integral()) {
        switch (type->get_basic_type_kind()) {
            case BasicTypeKind::CHAR:
                return 1;
            case BasicTypeKind::SHORT:
                return 2;
            case BasicTypeKind::INT:
                return 3;
            case BasicTypeKind::LONG:
                return 4;
            default:
                SemanticError::raise(loc, "Unknown basic type kind");
                return -1;
        }
    } else if (type->is_pointer()) {
        return 5; // Arbitrary higher precision for pointers
    } else {
        SemanticError::raise(loc, "Cannot determine precision of non-integral type");
        return -1;
    }
}

std::shared_ptr<Type> SemanticAnalysis::get_int_type() {
    return std::make_shared<BasicType>(BasicTypeKind::INT, true);
}

std::shared_ptr<Type> SemanticAnalysis::get_ptrdiff_t_type() {
    return std::make_shared<BasicType>(BasicTypeKind::LONG, true);
}

void SemanticAnalysis::is_less_precise(Node *left_node, Node *right_node, Node *expr_node) {
    std::shared_ptr<Type> left_type = left_node->get_type();
    std::shared_ptr<Type> right_type = right_node->get_type();

    bool left_is_signed = left_type->is_signed();
    bool right_is_signed = right_type->is_signed();

    int left_precision = determine_precision(left_type.get(), left_node->get_loc());
    int right_precision = determine_precision(right_type.get(), right_node->get_loc());

    // Promote types to int if less precise
    if (left_precision < determine_precision(get_int_type().get(), left_node->get_loc())) {
        left_node = promote_to_int(left_node);
        left_type = left_node->get_type();
        left_precision = determine_precision(left_type.get(), left_node->get_loc());
    }
    if (right_precision < determine_precision(get_int_type().get(), right_node->get_loc())) {
        right_node = promote_to_int(right_node);
        right_type = right_node->get_type();
        right_precision = determine_precision(right_type.get(), right_node->get_loc());
    }

    // Update nodes in the expression tree
    expr_node->set_kid(1, left_node);
    expr_node->set_kid(2, right_node);

    std::shared_ptr<Type> common_type;

    if (left_precision > right_precision) {
        common_type = left_type;
        right_node = implicit_conversion(right_node, common_type);
        expr_node->set_kid(2, right_node);
    } else if (right_precision > left_precision) {
        common_type = right_type;
        left_node = implicit_conversion(left_node, common_type);
        expr_node->set_kid(1, left_node);
    } else {
        if (left_is_signed == right_is_signed) {
            common_type = left_type;
        } else if (!left_is_signed && right_is_signed) {
            if (left_precision >= right_precision) {
                common_type = left_type;
                right_node = implicit_conversion(right_node, common_type);
                expr_node->set_kid(2, right_node);
            } else {
                common_type = right_type;
                left_node = implicit_conversion(left_node, common_type);
                expr_node->set_kid(1, left_node);
            }
        } else if (left_is_signed && !right_is_signed) {
            if (right_precision >= left_precision) {
                common_type = right_type;
                left_node = implicit_conversion(left_node, common_type);
                expr_node->set_kid(1, left_node);
            } else {
                common_type = left_type;
                right_node = implicit_conversion(right_node, common_type);
                expr_node->set_kid(2, right_node);
            }
        }
    }

    expr_node->set_type(common_type);
}