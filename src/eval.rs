use core::ascii;
use std::cell::RefCell;
use std::collections::HashMap;
use std::mem::discriminant;
use std::rc::Rc;

use anyhow::{Context, Result, bail, ensure};

use crate::ast::{Expression, Identifier, Node};
use crate::object::{
    Environment, HashObject, Object, ObjectInterface, create_false, create_null, create_true,
};
use crate::{ast, builtins, object};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum EvalError {
    #[error("identifier not found: `{ident}`.")]
    IdentifierNotFound { ident: Identifier },

    #[error("operation type mismatch: {left} {operator} {right}.")]
    OperationTypeMismatch {
        operator: String,
        left: String,
        right: String,
    },

    #[error("unknown operator `{operator}` for {operand_type}.")]
    UnknownOperator {
        operator: String,
        operand_type: String,
    },

    #[error("`{got}` is not a function.")]
    NotFunction { got: String },

    #[error("index operator not supported: {left}[{index}].")]
    UnsupportedIndexOperation { left: String, index: String },

    #[error("cannot use {got} as a hash key.")]
    NotHashable { got: String },

    #[error("{expr} didn't produce value.")]
    NotProducedValue { expr: Expression },
}

pub fn eval<T: ast::NodeInterface>(
    node: &T,
    env: Rc<RefCell<Environment>>,
) -> Result<Option<Rc<object::Object>>> {
    env.borrow_mut()
        .set("len", Rc::new(Object::builtin(builtins::len)));
    env.borrow_mut()
        .set("first", Rc::new(Object::builtin(builtins::first)));
    env.borrow_mut()
        .set("last", Rc::new(Object::builtin(builtins::last)));
    env.borrow_mut()
        .set("push", Rc::new(Object::builtin(builtins::push)));
    env.borrow_mut()
        .set("puts", Rc::new(Object::builtin(builtins::puts)));

    __eval(node, env)
}

fn __eval<T: ast::NodeInterface>(
    node: &T,
    env: Rc<RefCell<Environment>>,
) -> Result<Option<Rc<object::Object>>> {
    match node.get_node() {
        // program
        Node::Program(program) => {
            let a = eval_program(program, env);
            println!("{a:?}");
            a
        }
        // statements
        Node::Statement(stmt) => match stmt {
            ast::Statement::Expression(x) => {
                __eval(x, env).context("failed to eval an expression statement.")
            }
            ast::Statement::Let(x) => __eval(x, env).context("failed to eval a let statement."),
            ast::Statement::Return(x) => {
                __eval(x, env).context("failed to eval a return statement.")
            }
        },
        Node::ExpressionStatement(expr_stmt) => {
            let value = __eval(&expr_stmt.value, env).context("failed to eval the expression.")?;

            if expr_stmt.has_semicolon {
                Ok(None)
            } else {
                Ok(value)
            }
        }
        Node::ReturnStatement(ret_stmt) => {
            let value =
                match __eval(&ret_stmt.value, env).context("failed to eval the return value.")? {
                    Some(x) => x,
                    None => bail!(EvalError::NotProducedValue {
                        expr: ret_stmt.value.clone()
                    }),
                };
            Ok(Some(Rc::new(Object::ret_val(value))))
        }
        Node::LetStatement(let_stmt) => {
            let value =
                match __eval(&let_stmt.value, env.clone()).context("failed to eval the value.")? {
                    Some(x) => x,
                    None => bail!(EvalError::NotProducedValue {
                        expr: let_stmt.value.clone()
                    }),
                };

            env.borrow_mut().set(let_stmt.name.value.as_str(), value);

            if let_stmt.has_semicolon {
                Ok(None)
            } else {
                Ok(Some(create_null()))
            }
        }
        // expressions
        //// general expressions
        Node::Expression(expr) => match expr {
            ast::Expression::BoolLiteral(x) => __eval(x, env).context("failed to eval a bool."),
            ast::Expression::Call(x) => __eval(x, env).context("failed to eval a call expression."),
            ast::Expression::Function(x) => __eval(x, env).context("failed to eval a function"),
            ast::Expression::Identifier(x) => {
                __eval(x, env).context("failed to eval an identifier")
            }
            ast::Expression::If(x) => __eval(x, env).context("failed to eval an if expression"),
            ast::Expression::Infix(x) => {
                __eval(x, env).context("failed to eval an infix expression")
            }
            ast::Expression::IntegerLiteral(x) => {
                __eval(x, env).context("failed to eval an integer.")
            }
            ast::Expression::Prefix(x) => {
                __eval(x, env).context("failed to eval a prefix expression")
            }
            ast::Expression::StringLiteral(x) => __eval(x, env).context("failed to eval a string."),
            ast::Expression::ArrayLiteral(x) => __eval(x, env).context("failed to eval an array."),
            ast::Expression::IndexExpression(x) => {
                __eval(x, env).context("failed to eval an index expression.")
            }
            ast::Expression::HashLiteral(x) => __eval(x, env).context("failed to eval a hash."),
            ast::Expression::BlockStatement(x) => {
                __eval(x, env).context("failed to eval a block statement.")
            }
        },
        //// prefix expression
        Node::PrefixExpression(prefix_expr) => {
            let right = match __eval(prefix_expr.right.as_ref(), env)
                .context("failed to eval the right expression.")?
            {
                Some(x) => x,
                None => {
                    bail!(EvalError::NotProducedValue {
                        expr: prefix_expr.right.as_ref().clone()
                    })
                }
            };

            let expr = eval_prefix_expression(&prefix_expr.operator, &right)?;

            Ok(Some(expr))
        }
        //// infix expression
        Node::InfixExpression(infix_expr) => {
            let left = match __eval(infix_expr.left.as_ref(), env.clone())
                .context("failed to eval the left expression.")?
            {
                Some(x) => x,
                None => bail!(EvalError::NotProducedValue {
                    expr: infix_expr.left.as_ref().clone()
                }),
            };

            let right = match __eval(infix_expr.right.as_ref(), env)
                .context("failed to eval the right expression.")?
            {
                Some(x) => x,
                None => {
                    bail!(EvalError::NotProducedValue {
                        expr: infix_expr.right.as_ref().clone()
                    })
                }
            };

            let expr = eval_infix_expression(&infix_expr.operator, &left, &right)?;

            Ok(Some(expr))
        }
        //// if-else
        Node::IfExpression(if_expr) => eval_if_expression(if_expr, env),
        Node::BlockStatement(block_stmt) => eval_block_statement(block_stmt, env),
        //// identifier
        Node::Identifier(ident) => Ok(Some(eval_identifier(ident, env)?)),
        //// function call
        Node::CallExpression(call_expr) => {
            let func = match __eval(call_expr.func.as_ref(), env.clone())
                .context("failed to eval the function identifier.")?
            {
                Some(x) => x,
                None => bail!(EvalError::NotProducedValue {
                    expr: call_expr.func.as_ref().clone()
                }),
            };

            let args =
                eval_expressions(&call_expr.args, env).context("failed to eval the arguments.")?;

            Ok(Some(
                apply_function(func, &args).context("failed to eval the function.")?,
            ))
        }
        //// index reference
        Node::IndexExpression(idx_expr) => {
            let left = match __eval(idx_expr.left.as_ref(), env.clone())
                .context("failed to eval the left expression.")?
            {
                Some(x) => x,
                None => bail!(EvalError::NotProducedValue {
                    expr: idx_expr.left.as_ref().clone()
                }),
            };

            let index = match __eval(idx_expr.index.as_ref(), env)
                .context("failed to eval the expression in the index operator.")?
            {
                Some(x) => x,
                None => bail!(EvalError::NotProducedValue {
                    expr: idx_expr.index.as_ref().clone()
                }),
            };

            Ok(Some(eval_index_expression(left, index)?))
        }

        //// literals
        Node::IntegerLiteral(int_literal) => Ok(Some(Rc::new(Object::int(int_literal.value)))),
        Node::BoolLiteral(bool_literal) => Ok(Some(Rc::new(Object::bool(bool_literal.value)))),
        Node::FunctionLiteral(func_literal) => {
            Ok(Some(Rc::new(Object::from_func_litereal(func_literal, env))))
        }
        Node::StringLiteral(literal) => Ok(Some(Rc::new(Object::str(&literal.value)))),
        Node::ArrayLiteral(literal) => {
            let elements = eval_expressions(&literal.elements, env)
                .context("failed to eval the element list.")?;
            Ok(Some(Rc::new(Object::Array(Rc::new(RefCell::new(
                object::Array::new(&elements),
            ))))))
        }
        Node::HashLiteral(literal) => Ok(Some(eval_hash_literal(literal, env)?)),
        _ => unimplemented!(),
    }
}

fn eval_program(
    program: &ast::Program,
    env: Rc<RefCell<Environment>>,
) -> Result<Option<Rc<object::Object>>> {
    let stmts = &program.statements;

    for (_, stmt) in stmts.iter().enumerate() {
        if let Some(value) = __eval(stmt, env.clone()).context("failed to evaluate a statement.")? {
            return Ok(Some(unwrap_return_value(value)));
        }
    }

    Ok(None)
}

fn eval_block_statement(
    block_stmt: &ast::BlockStatement,
    env: Rc<RefCell<Environment>>,
) -> Result<Option<Rc<Object>>> {
    let stmts = &block_stmt.statements;

    for (_, stmt) in stmts.iter().enumerate() {
        if let Some(value) = __eval(stmt, env.clone()).context("failed to evaluate a statement.")? {
            return Ok(Some(value));
        }
    }

    return Ok(None);
}

// prefix
fn eval_prefix_expression(operator: &str, right: &object::Object) -> Result<Rc<object::Object>> {
    match operator {
        "!" => Ok(eval_exclamation_operator_expression(right)),
        "-" => Ok(eval_minus_prefix_operator_expression(right)
            .context("failed to eval the minus operator expression.")?),
        _ => bail!(EvalError::UnknownOperator {
            operator: operator.to_string(),
            operand_type: right.get_name()
        }),
    }
}

fn eval_exclamation_operator_expression(right: &object::Object) -> Rc<object::Object> {
    match right {
        object::Object::Bool(bool_obj) => {
            if bool_obj.borrow().value {
                create_false()
            } else {
                create_true()
            }
        }
        object::Object::Null(_) => create_true(),
        _ => create_false(),
    }
}

fn eval_minus_prefix_operator_expression(right: &object::Object) -> Result<Rc<object::Object>> {
    if let object::Object::Integer(int_obj) = right {
        return Ok(Rc::new(Object::int(-int_obj.borrow().value)));
    }

    bail!(EvalError::UnknownOperator {
        operator: "-".to_string(),
        operand_type: right.get_name()
    })
}

// infix
fn eval_infix_expression(
    operator: &str,
    left: &object::Object,
    right: &object::Object,
) -> Result<Rc<object::Object>> {
    ensure!(
        discriminant(left) == discriminant(right),
        EvalError::OperationTypeMismatch {
            operator: operator.to_string(),
            left: left.get_name(),
            right: right.get_name()
        }
    );

    match operator {
        "==" => Ok(Rc::new(Object::bool(*right == *left))),
        "!=" => Ok(Rc::new(Object::bool(*right != *left))),
        _ => {
            if let (object::Object::Integer(x), object::Object::Integer(y)) = (left, right) {
                return eval_integer_infix_expression(operator, &x.borrow(), &y.borrow())
                    .context("failed to eval the integer infix expression.");
            }

            if let (Object::String(x), Object::String(y)) = (left, right) {
                return eval_string_infix_expression(operator, &x.borrow(), &y.borrow())
                    .context("failed to eval the string infix expression.");
            }

            bail!(EvalError::UnknownOperator {
                operator: operator.to_string(),
                operand_type: left.get_name()
            });
        }
    }
}

fn eval_integer_infix_expression(
    operator: &str,
    left: &object::IntegerObject,
    right: &object::IntegerObject,
) -> Result<Rc<object::Object>> {
    match operator {
        "+" => Ok(Rc::new(Object::int(left.value + right.value))),
        "-" => Ok(Rc::new(Object::int(left.value - right.value))),
        "*" => Ok(Rc::new(Object::int(left.value * right.value))),
        "/" => Ok(Rc::new(Object::int(left.value / right.value))),
        "<" => Ok(Rc::new(Object::bool(left.value < right.value))),
        ">" => Ok(Rc::new(Object::bool(left.value > right.value))),
        "==" => Ok(Rc::new(Object::bool(left.value == right.value))),
        "!=" => Ok(Rc::new(Object::bool(left.value != right.value))),
        _ => bail!(EvalError::UnknownOperator {
            operator: operator.to_string(),
            operand_type: left.get_name()
        }),
    }
}

fn eval_string_infix_expression(
    operator: &str,
    left: &object::StringObject,
    right: &object::StringObject,
) -> Result<Rc<Object>> {
    ensure!(
        operator == "+",
        EvalError::UnknownOperator {
            operator: operator.to_string(),
            operand_type: left.get_name()
        }
    );

    Ok(Rc::new(Object::str(&format!(
        "{}{}",
        left.value.as_str(),
        right.value.as_str()
    ))))
}

// if-else
fn eval_if_expression(
    if_expr: &ast::IfExpression,
    env: Rc<RefCell<Environment>>,
) -> Result<Option<Rc<Object>>> {
    let condition = match __eval(if_expr.condition.as_ref(), env.clone())
        .context("failed to eval the condition.")?
    {
        Some(x) => x,
        None => bail!(EvalError::NotProducedValue {
            expr: if_expr.condition.as_ref().clone()
        }),
    };

    if let Some(alternative) = &if_expr.alternative {
        if is_truethy(condition) {
            return __eval(&if_expr.consequence, env)
                .context("failed to eval the consequence block.");
        } else {
            return __eval(alternative, env).context("failed to eval the alternative block.");
        }
    }

    if is_truethy(condition) {
        match __eval(&if_expr.consequence, env).context("failed to eval the consequence block.")? {
            Some(value) if value.is_returned() => return Ok(Some(value)),
            _ => (),
        }
    }

    Ok(None)
}

fn is_truethy(obj: Rc<object::Object>) -> bool {
    match &*obj {
        Object::Bool(b) => b.borrow().value,
        Object::Null(_) => false,
        _ => true,
    }
}

// let
fn eval_identifier(ident: &ast::Identifier, env: Rc<RefCell<Environment>>) -> Result<Rc<Object>> {
    if let Some(value) = env.borrow().get(ident.value.as_str()) {
        return Ok(value);
    }

    bail!(EvalError::IdentifierNotFound {
        ident: ident.clone()
    });
}

// index expression
fn eval_index_expression(left: Rc<Object>, index: Rc<Object>) -> Result<Rc<Object>> {
    match (&*left, &*index) {
        (Object::Array(array), Object::Integer(integer)) => {
            eval_array_index_expression(array.clone(), integer.clone())
                .context("failed to eval the array index expression.")
        }
        (Object::Hash(hash_obj), _) => eval_hash_index_expression(hash_obj.clone(), index)
            .context("failed to eval the hash index expression."),
        _ => bail!(EvalError::UnsupportedIndexOperation {
            left: left.get_name(),
            index: index.get_name()
        }),
    }
}

fn eval_array_index_expression(
    array: Rc<RefCell<object::Array>>,
    index: Rc<RefCell<object::IntegerObject>>,
) -> Result<Rc<Object>> {
    let value = match array.borrow().array.get(index.borrow().value as usize) {
        Some(x) => x.clone(),
        None => create_null(),
    };

    Ok(value)
}

fn eval_hash_index_expression(
    hash_obj: Rc<RefCell<HashObject>>,
    key_obj: Rc<Object>,
) -> Result<Rc<Object>> {
    let key = object::HashKeyObject::from_object(key_obj)?;

    let value = match hash_obj.borrow().pairs.get(&key) {
        Some(x) => x.clone(),
        None => create_null(),
    };

    Ok(value)
}

// hash
fn eval_hash_literal(
    hash_literal: &ast::HashLiteral,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let mut pairs = HashMap::new();

    for (i, (key, value)) in hash_literal.pairs.iter().enumerate() {
        let key_obj = match __eval(key, env.clone())
            .with_context(|| format!("failed to eval a key at index {}.", i))?
        {
            Some(x) => x,
            None => bail!(EvalError::NotProducedValue { expr: key.clone() }),
        };

        let value_obj = match __eval(value, env.clone())
            .with_context(|| format!("failed to eval a value at index {}.", i))?
        {
            Some(x) => x,
            None => bail!(EvalError::NotProducedValue {
                expr: value.clone()
            }),
        };

        pairs.insert(object::HashKeyObject::from_object(key_obj)?, value_obj);
    }

    Ok(Rc::new(Object::Hash(Rc::new(RefCell::new(
        object::HashObject::new(pairs),
    )))))
}

//
fn eval_expressions(
    expressions: &[ast::Expression],
    env: Rc<RefCell<Environment>>,
) -> Result<Vec<Rc<Object>>> {
    let mut objs = Vec::new();

    for (i, expr) in expressions.iter().enumerate() {
        let evaluated = match __eval(expr, env.clone())
            .with_context(|| format!("failed to eval an expression at index {i}"))?
        {
            Some(x) => x,
            None => bail!(EvalError::NotProducedValue { expr: expr.clone() }),
        };

        objs.push(evaluated);
    }

    Ok(objs)
}

// related to function
fn apply_function(f: Rc<Object>, args: &[Rc<Object>]) -> Result<Rc<Object>> {
    match &*f {
        Object::Function(func) => {
            let func_env = func
                .borrow()
                .create_function_env(args)
                .context("failed to create the environment.")?;

            let evaluated =
                match __eval(&func.borrow().body, func_env).context("failed to eval the body.")? {
                    Some(x) => x,
                    None => bail!(EvalError::NotProducedValue {
                        expr: Expression::BlockStatement(func.borrow().body.clone())
                    }),
                };

            Ok(unwrap_return_value(evaluated))
        }
        Object::Builtin(builtin) => {
            (builtin.borrow().func)(args).context("failed to run a builtin function.")
        }
        _ => bail!(EvalError::NotFunction { got: f.get_name() }),
    }
}

fn unwrap_return_value(obj: Rc<Object>) -> Rc<Object> {
    match &*obj {
        Object::ReturnValue(r) => r.borrow().value.clone(),
        _ => obj,
    }
}

mod test {
    use std::cell::RefCell;
    use std::mem::discriminant;
    use std::rc::Rc;

    use anyhow::{Result, bail};

    use crate::ast::NodeInterface;
    use crate::lexer::Lexer;
    use crate::object::{self, Environment, HashKeyObject, Object};
    use crate::parser::Parser;
    use crate::utils::print_errors;

    use super::eval;

    #[test]
    fn test_eval_integer_expression() {
        #[derive(Debug)]
        struct Test {
            input: String,
            expected: i64,
        }
        impl Test {
            fn new(input: &str, expected: i64) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("5", 5),
            Test::new("10", 10),
            Test::new("-5", -5),
            Test::new("-10", -10),
            Test::new("5 + 5 + 5 + 5 - 10", 10),
            Test::new("2 * 2 * 2 * 2 * 2", 32),
            Test::new("-50 + 100 + -50", 0),
            Test::new("5 * 2 + 10", 20),
            Test::new("5 + 2 * 10", 25),
            Test::new("20 + 2 * -10", 0),
            Test::new("50 / 2 * 2 + 10", 60),
            Test::new("2 * (5 + 10)", 30),
            Test::new("3 * 3 * 3 + 10", 37),
            Test::new("3 * (3 * 3) + 10", 37),
            Test::new("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];

        for (i, test) in tests.iter().enumerate() {
            let obj = test_eval(&test.input).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });
            test_integer_object(&obj, test.expected).unwrap_or_else(|err| {
                panic!("test {i} failed: {}", err);
            });
        }
    }

    #[test]
    fn test_eval_bool_expression() {
        struct Test {
            input: String,
            expected: bool,
        }
        impl Test {
            fn new(input: &str, expected: bool) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("true", true),
            Test::new("false", false),
            Test::new("true == true", true),
            Test::new("false == false", true),
            Test::new("true == false", false),
            Test::new("true != false", true),
            Test::new("false != true", true),
            Test::new("(1 < 2) == true", true),
            Test::new("(1 < 2) == false", false),
            Test::new("(1 > 2) == true", false),
            Test::new("(1 > 2) == false", true),
        ];

        for (i, test) in tests.iter().enumerate() {
            let obj = test_eval(&test.input).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });
            test_bool_object(&obj, test.expected);
        }
    }

    #[test]
    fn test_eval_exclamation_operator() {
        struct Test {
            input: String,
            expected: bool,
        }
        impl Test {
            fn new(input: &str, expected: bool) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("!true", false),
            Test::new("!false", true),
            Test::new("!5", false),
            Test::new("!!true", true),
            Test::new("!!false", false),
            Test::new("!!5", true),
        ];

        for (i, test) in tests.iter().enumerate() {
            let obj = test_eval(&test.input).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });
            test_bool_object(&obj, test.expected);
        }
    }

    #[test]
    fn test_if_else_expressoin() {
        #[derive(Debug)]
        struct Test {
            input: String,
            expected: Option<Object>,
        }
        impl Test {
            fn new(input: &str, expected: Option<Object>) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("if (true) { 10 }", None),
            Test::new("if (false) { 10 }", None),
            Test::new("if (1) { 10 }", None),
            Test::new("if (1 < 2) { 10 }", None),
            Test::new("if (1 > 2) { 10 }", None),
            Test::new(
                "if (1 > 2) { 10 } else { 20 }",
                Some(object::Object::int(20)),
            ),
            Test::new(
                "if (1 < 2) { 10 } else { 20 }",
                Some(object::Object::int(10)),
            ),
        ];

        for (i, test) in tests.iter().enumerate() {
            let result = test_eval(&test.input);

            if result.is_some() && test.expected.is_none() {
                panic!(
                    "expected that no value is produced. got: {:?}",
                    result.unwrap()
                );
            }

            if result.is_none() && test.expected.is_some() {
                panic!(
                    "no value is produced. expected: {}",
                    test.expected.as_ref().unwrap()
                );
            }

            if let Some(obj) = result {
                let r = match &test.expected.as_ref().unwrap() {
                    object::Object::Bool(b) => test_bool_object(&obj, b.borrow().value),
                    object::Object::Integer(i) => test_integer_object(&obj, i.borrow().value),
                    object::Object::Null(n) => test_null_object(&obj),
                    object::Object::ReturnValue(_) => panic!("program returned ReturnValue."),
                    _ => unimplemented!(),
                };
                r.unwrap_or_else(|err| {
                    panic!("test {} failed. got: {}", i, err);
                });
            }
        }
    }

    #[test]
    fn test_return_statement() {
        struct Test {
            input: String,
            expected: i64,
        }
        impl Test {
            fn new(input: &str, expected: i64) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("return 10;", 10),
            Test::new("return 10; 9;", 10),
            Test::new("return 2 * 5; 9;", 10),
            Test::new("9; return 2 * 5; 9;", 10),
            Test::new(
                "if (10 > 1) {
                  if (10 > 1) {
                    return 10;
                  }

                  return 1;
                }",
                10,
            ),
        ];

        for (i, test) in tests.iter().enumerate() {
            let obj = test_eval(&test.input).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });
            test_integer_object(&obj, test.expected).unwrap_or_else(|err| {
                panic!("test {} failed: {}", i, err);
            });
        }
    }

    #[test]
    fn test_let_statements() {
        struct Test {
            input: String,
            expected: i64,
        }
        impl Test {
            fn new(input: &str, expected: i64) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("let a = 5; a", 5),
            Test::new("let a = 5 * 5; a", 25),
            Test::new("let a = 5; let b = a; b", 5),
            Test::new("let a = 5; let b = a; let c = a + b + 5; c", 15),
        ];

        for (i, test) in tests.iter().enumerate() {
            let obj = test_eval(&test.input).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });
            test_integer_object(&obj, test.expected).unwrap_or_else(|err| {
                panic!("test {i} failed: {err}.",);
            });
        }
    }

    #[test]
    fn test_function_object() {
        let input = "fn(x) { x + 2; }";

        let evaluated = &*test_eval(input).unwrap_or_else(|| {
            panic!("no value is produced.");
        });

        let fn_obj = if let Object::Function(x) = evaluated {
            x
        } else {
            panic!("object is not Function. got: {evaluated:?}");
        };

        if fn_obj.borrow().params.len() != 1 {
            panic!("number of parameter for function is wrong.");
        }

        if fn_obj.borrow().params[0].to_string().as_str() != "x" {
            panic!("parameter is not 'x'");
        }

        let expected_body = "{(x + 2);}";

        if fn_obj.borrow().body.to_string().as_str() != expected_body {
            panic!(
                "body is not {expected_body}. got: {}",
                fn_obj.borrow().body.to_string()
            );
        }
    }

    #[test]
    fn test_function_application() {
        struct Test {
            input: String,
            expected: i64,
        }
        impl Test {
            fn new(input: &str, expected: i64) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("let identity = fn(x) { x }; identity(5)", 5),
            Test::new("let identity = fn(x) { return x; }; identity(5)", 5),
            Test::new("let double = fn(x) { x * 2 }; double(5)", 10),
            Test::new("let add = fn(x, y) { x + y }; add(5, 5)", 10),
            Test::new("let add = fn(x, y) { x + y }; add(5 + 5, add(5, 5))", 20),
            Test::new("fn(x) { x }(5)", 5),
        ];

        for (i, test) in tests.iter().enumerate() {
            let evaluated = &*test_eval(test.input.as_str()).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });

            test_integer_object(evaluated, test.expected).unwrap_or_else(|err| {
                print_errors("test {i} failed", err);
                panic!();
            });
        }
    }

    #[test]
    fn est_closures() {
        let input = "
            let newAdder = fn(x) {
              fn(y) { x + y }
            };

            let addTwo = newAdder(2);
            addTwo(2)
            ";

        let evaluated = &*test_eval(input).unwrap_or_else(|| {
            panic!("no value is produced.");
        });

        test_integer_object(evaluated, 4).unwrap_or_else(|err| {
            print_errors("test failed.", err);
            panic!()
        });
    }

    #[test]
    fn test_string_literal() {
        let input = "\"Hello World!\"";

        let evaluated = &*test_eval(input).unwrap_or_else(|| {
            panic!("no value is produced.");
        });

        let str_obj = if let Object::String(l) = evaluated {
            l
        } else {
            panic!("object is not StringLiteral");
        };

        if str_obj.borrow().value.as_str() != "Hello World!" {
            panic!(
                "literal.value is not \"Hello World!\". got: {}",
                str_obj.borrow().value.as_str()
            );
        }
    }

    #[test]
    fn test_string_concatenation() {
        let input = "\"Hello\" + \" \" + \"World!\"";

        let evaluated = &*test_eval(input).unwrap_or_else(|| {
            panic!("no value is produced.");
        });

        let str_obj = if let Object::String(l) = evaluated {
            l
        } else {
            panic!("object is not StringLiteral");
        };

        if str_obj.borrow().value.as_str() != "Hello World!" {
            panic!(
                "literal.value is not \"Hello World!\". got: {}",
                str_obj.borrow().value.as_str()
            );
        }
    }

    #[test]
    fn test_builtin_functions() {
        struct Test {
            input: String,
            expected: i64,
        }
        impl Test {
            fn new(input: &str, expected: i64) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("len(\"\")", 0),
            Test::new("len(\"four\")", 4),
            Test::new("len(\"hello world\")", 11),
        ];

        for (i, test) in tests.iter().enumerate() {
            let evaluated = &*test_eval(&test.input).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });

            if !matches!(evaluated, Object::Integer(_)) {
                panic!("test {i} failed: object is not integer: {evaluated:?}");
            }

            test_integer_object(evaluated, test.expected).unwrap_or_else(|err| {
                print_errors(format!("test {i} failed.").as_str(), err);
                panic!();
            });
        }
    }

    #[test]
    fn test_array_literals() {
        let input = "[1, 2 * 2, 3 + 3]";

        let evaluated = &*test_eval(input).unwrap_or_else(|| {
            panic!("no value is produced.");
        });

        let array = if let Object::Array(array) = evaluated {
            array
        } else {
            panic!("the object is not Array. got: {evaluated:?}",);
        };

        if array.borrow().array.len() != 3 {
            panic!(
                "the length of array is not 3. got: {}",
                array.borrow().array.len()
            );
        }

        test_integer_object(&array.borrow().array[0], 1);
        test_integer_object(&array.borrow().array[1], 4);
        test_integer_object(&array.borrow().array[2], 6);
    }

    #[test]
    fn test_array_index_expressions() {
        #[derive(Debug)]
        struct Test {
            input: String,
            expected: Object,
        }
        impl Test {
            fn new(input: &str, expected: Object) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("[1, 2, 3][0]", Object::int(1)),
            Test::new("[1, 2, 3][1]", Object::int(2)),
            Test::new("[1, 2, 3][2]", Object::int(3)),
            Test::new("let i = 0; [1][i]", Object::int(1)),
            Test::new("[1, 2, 3][1 + 1]", Object::int(3)),
            Test::new("let myArray = [1, 2, 3]; myArray[2]", Object::int(3)),
            Test::new(
                "let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2]",
                Object::int(6),
            ),
            Test::new(
                "let myArray = [1, 2, 3]; let i = myArray[0]; myArray[i]",
                Object::int(2),
            ),
            Test::new("[1, 2, 3][3]", Object::null()),
            Test::new("[1, 2, 3][-1]", Object::null()),
        ];

        for (i, test) in tests.iter().enumerate() {
            let evaluated = &*test_eval(&test.input).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });

            match (evaluated, &test.expected) {
                (Object::Integer(_), Object::Integer(y)) => {
                    test_integer_object(evaluated, y.borrow().value).unwrap_or_else(|err| {
                        print_errors(format!("test {} failed.", i).as_str(), err);
                        panic!();
                    })
                }
                (Object::Null(_), Object::Null(_)) => {}
                _ => panic!(
                    "unexpected or unsupported objects. evaluated: {:?}, expected: {:?}",
                    evaluated, &test.expected
                ),
            }
        }
    }

    #[test]
    fn test_hash_literals() {
        let input = "let two = \"two\";
            {
                \"one\": 10 - 9,
                two: 1 + 1,
                \"thr\" + \"ee\": 6 / 2,
                4: 4,
                true: 5,
                false: 6
            }";

        let expected = vec![
            (HashKeyObject::str("one"), 1),
            (HashKeyObject::str("two"), 2),
            (HashKeyObject::str("three"), 3),
            (HashKeyObject::int(4), 4),
            (HashKeyObject::bool(true), 5),
            (HashKeyObject::bool(false), 6),
        ];

        let evaluated = &*test_eval(input).unwrap_or_else(|| {
            panic!("no value is produced.");
        });

        let hash_obj = if let Object::Hash(x) = evaluated {
            x
        } else {
            panic!("evaluated is not HashObject. got: {evaluated:?}");
        }
        .borrow();

        if expected.len() != hash_obj.pairs.len() {
            panic!(
                "length of expected and length of evaluated is not same. expected: {}. got: {}",
                expected.len(),
                hash_obj.pairs.len()
            );
        }

        for (i, (expected_key, expected_value)) in expected.iter().enumerate() {
            let value = hash_obj.pairs.get(expected_key).unwrap_or_else(|| {
                panic!(
                    "test {} failed. no value associated to {}.",
                    i, expected_key
                );
            });

            test_integer_object(value, *expected_value).unwrap_or_else(|err| {
                print_errors(format!("test {} failed", i).as_str(), err);
                panic!()
            });
        }
    }

    #[test]
    fn test_hash_index_expression() {
        #[derive(Debug)]
        struct Test {
            input: String,
            expected: Object,
        }
        impl Test {
            fn new(input: &str, expected: Object) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("{\"foo\": 5}[\"foo\"]", Object::int(5)),
            Test::new("{\"foo\": 5}[\"bar\"]", Object::null()),
            Test::new("let key = \"foo\"; {\"foo\": 5}[key]", Object::int(5)),
            Test::new("{}[\"foo\"]", Object::null()),
            Test::new("{5: 5}[5]", Object::int(5)),
            Test::new("{true: 5}[true]", Object::int(5)),
            Test::new("{false: 5}[false]", Object::int(5)),
        ];

        for (i, test) in tests.iter().enumerate() {
            let evaluated = &*test_eval(&test.input).unwrap_or_else(|| {
                panic!("test {i} failed: no value is produced.");
            });

            match (evaluated, &test.expected) {
                (Object::Integer(x), Object::Integer(y)) => {
                    test_integer_object(evaluated, y.borrow().value).unwrap_or_else(|err| {
                        print_errors(format!("test {} failed", i).as_str(), err);
                        panic!()
                    })
                }
                (Object::Null(_), Object::Null(_)) => {}
                (x, y) => {
                    panic!("test {i} failed. expected: {y:?}, got: {x:?}");
                }
            }
        }
    }

    fn test_eval(input: &str) -> Option<Rc<object::Object>> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(err) => {
                print_errors("failed to parse the program", err);
                panic!();
            }
        };

        let env = Rc::new(RefCell::new(Environment::new(None)));

        eval(&program, env).unwrap_or_else(|e| {
            print_errors("failed to evaluate", e);
            panic!()
        })
    }

    fn test_integer_object(obj: &Object, expected: i64) -> Result<()> {
        let int_obj = if let Object::Integer(int_obj) = obj {
            int_obj
        } else {
            bail!("obj is not Integer. got: {obj:?}");
        };

        if int_obj.borrow().value != expected {
            bail!(
                "int_obj.value is not {expected}. got: {}",
                int_obj.borrow().value
            );
        }

        Ok(())
    }

    fn test_bool_object(obj: &Object, expected: bool) -> Result<()> {
        let bool_obj = if let Object::Bool(bool_obj) = obj {
            bool_obj
        } else {
            bail!("obj is not Bool. got: {obj:?}");
        };

        if bool_obj.borrow().value != expected {
            bail!(
                "bool_obj.value is not {expected}. got: {}",
                bool_obj.borrow().value
            );
        }

        Ok(())
    }

    fn test_null_object(obj: &Object) -> Result<()> {
        if let object::Object::Null(_) = obj {
            Ok(())
        } else {
            bail!("obj is not Null. got: {obj}");
        }
    }
}
