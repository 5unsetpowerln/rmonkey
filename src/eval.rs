use core::ascii;

use anyhow::{Context, Result, anyhow};

use crate::ast::{Node, NodeInterface};
use crate::object::{FALSE, NULL, TRUE};
use crate::{ast, object};

pub fn eval<T: ast::NodeInterface>(node: &T) -> Result<object::Object> {
    match node.get_node() {
        // program
        Node::Program(program) => eval_statements(&program.statements),
        // statements
        Node::Statement(stmt) => match stmt {
            ast::Statement::Expression(x) => eval(x),
            ast::Statement::Let(x) => eval(x),
            ast::Statement::Return(x) => eval(x),
        },
        Node::ExpressionStatement(expr_stmt) => eval(&expr_stmt.value),
        // expressions
        Node::Expression(expr) => match expr {
            ast::Expression::BoolLiteral(x) => eval(x),
            ast::Expression::Call(x) => eval(x),
            ast::Expression::Function(x) => eval(x),
            ast::Expression::Identifier(x) => eval(x),
            ast::Expression::If(x) => eval(x),
            ast::Expression::Infix(x) => eval(x),
            ast::Expression::IntegerLiteral(x) => eval(x),
            ast::Expression::Prefix(x) => eval(x),
        },
        Node::IntegerLiteral(int_literal) => Ok(object::Object::Integer(object::Integer::new(
            int_literal.value,
        ))),
        Node::PrefixExpression(prefix_expr) => {
            let right = eval(&*prefix_expr.right)
                .context("failed to eval right expression")
                .context("failed to eval prefix expression")?;

            let obj = eval_prefix_expression(&prefix_expr.operator, &right);

            Ok(obj)
        }
        Node::BoolLiteral(bool_literal) => {
            Ok(object::Object::Bool(object::Bool::new(bool_literal.value)))
        }
        _ => unimplemented!(),
    }
}

fn eval_statements(statements: &[ast::Statement]) -> Result<object::Object> {
    if statements.is_empty() {
        return Err(anyhow!("statements is empty."));
    }

    for (i, stmt) in statements.iter().enumerate() {
        let result = eval(stmt).context("failed to evaluate a statement.")?;

        if i == statements.len() - 1 {
            return Ok(result);
        }
    }

    unreachable!()
}

fn eval_prefix_expression(operator: &[ascii::Char], right: &object::Object) -> object::Object {
    match operator.as_str() {
        "!" => eval_exclamation_expression(right),
        _ => NULL.clone(),
    }
}

fn eval_exclamation_expression(right: &object::Object) -> object::Object {
    match right {
        object::Object::Bool(bool_obj) => {
            if bool_obj.value {
                FALSE.clone()
            } else {
                TRUE.clone()
            }
        }
        object::Object::Null(_) => TRUE.clone(),
        _ => FALSE.clone(),
    }
}

mod test {
    use std::ascii;

    use crate::lexer::Lexer;
    use crate::object::{self, Object};
    use crate::parser::Parser;

    use super::eval;

    #[test]
    fn test_eval_integer_expression() {
        struct Test {
            input: Vec<ascii::Char>,
            expected: i64,
        }
        impl Test {
            fn new(input: &str, expected: i64) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    expected,
                }
            }
        }

        let tests = vec![Test::new("5", 5), Test::new("10", 10)];

        for test in tests.iter() {
            let obj = test_eval(&test.input);
            test_integer_object(&obj, test.expected);
        }
    }

    #[test]
    fn test_eval_bool_expression() {
        struct Test {
            input: Vec<ascii::Char>,
            expected: bool,
        }
        impl Test {
            fn new(input: &str, expected: bool) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    expected,
                }
            }
        }

        let tests = vec![Test::new("true", true), Test::new("false", false)];

        for test in tests.iter() {
            let obj = test_eval(&test.input);
            test_bool_object(&obj, test.expected);
        }
    }

    #[test]
    fn test_exclamation_operator() {
        struct Test {
            input: Vec<ascii::Char>,
            expected: bool,
        }
        impl Test {
            fn new(input: &str, expected: bool) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
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

        for test in tests.iter() {
            let obj = test_eval(&test.input);
            test_bool_object(&obj, test.expected);
        }
    }

    fn test_eval(input: &[ascii::Char]) -> object::Object {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program().unwrap_or_else(|_| {
            parser.print_errors();
            panic!("failed to parse.");
        });

        eval(&program).unwrap_or_else(|e| {
            panic!("failed to evaluate: {e}");
        })
    }

    fn test_integer_object(obj: &Object, expected: i64) {
        let int_obj = if let Object::Integer(int_obj) = obj {
            int_obj
        } else {
            panic!("obj is not Integer. got: {obj:?}")
        };

        if int_obj.value != expected {
            panic!("int_obj.value is not {expected}. got: {}", int_obj.value);
        }
    }

    fn test_bool_object(obj: &Object, expected: bool) {
        let bool_obj = if let Object::Bool(bool_obj) = obj {
            bool_obj
        } else {
            panic!("obj is not Bool. got: {obj:?}");
        };

        if bool_obj.value != expected {
            panic!("bool_obj.value is not {expected}. got: {}", bool_obj.value);
        }
    }
}
