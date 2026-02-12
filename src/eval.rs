use core::ascii;
use std::mem::discriminant;

use anyhow::{Context, Result, anyhow, bail};

use crate::ast::{Node, NodeInterface};
use crate::object::{Environment, FALSE, NULL, Object, TRUE};
use crate::{ast, object};

pub fn eval<T: ast::NodeInterface>(node: &T, env: &mut Environment) -> Result<object::Object> {
    match node.get_node() {
        // program
        Node::Program(program) => eval_program(program, env),
        // statements
        Node::Statement(stmt) => match stmt {
            ast::Statement::Expression(x) => eval(x, env),
            ast::Statement::Let(x) => eval(x, env),
            ast::Statement::Return(x) => eval(x, env),
        },
        Node::ExpressionStatement(expr_stmt) => eval(&expr_stmt.value, env),
        Node::ReturnStatement(ret_stmt) => {
            let value = eval(&ret_stmt.value, env)
                .context("failed to eval expression for return value.")?;
            Ok(Object::ret_val(value))
        }
        Node::LetStatement(let_stmt) => {
            let value = eval(&let_stmt.value, env)
                .context("failed to eval value for let statement.")
                .context("failed to eval let statement.")?;
            env.set(let_stmt.name.value.as_str(), value);
            Ok(NULL.clone())
        }
        // expressions
        //// general expressions
        Node::Expression(expr) => match expr {
            ast::Expression::BoolLiteral(x) => eval(x, env),
            ast::Expression::Call(x) => eval(x, env),
            ast::Expression::Function(x) => eval(x, env),
            ast::Expression::Identifier(x) => eval(x, env),
            ast::Expression::If(x) => eval(x, env),
            ast::Expression::Infix(x) => eval(x, env),
            ast::Expression::IntegerLiteral(x) => eval(x, env),
            ast::Expression::Prefix(x) => eval(x, env),
        },
        //// prefix expression
        Node::PrefixExpression(prefix_expr) => {
            let right = eval(&*prefix_expr.right, env)
                .context("failed to eval right expression")
                .context("failed to eval prefix expression")?;

            eval_prefix_expression(&prefix_expr.operator, &right)
                .context("failed to eval prefix expression")
        }
        //// infix expression
        Node::InfixExpression(infix_expr) => {
            let left = eval(&*infix_expr.left, env)
                .context("failed to eval left expression")
                .context("failed to eval infix expression")?;
            let right = eval(&*infix_expr.right, env)
                .context("failed to eval right expression")
                .context("failed to eval infix expression")?;
            eval_infix_expression(&infix_expr.operator, &left, &right)
                .context("failed to eval infix expression")
        }
        //// if-else
        Node::IfExpression(if_expr) => eval_if_expression(if_expr, env),
        Node::BlockStatement(block_stmt) => eval_block_statement(block_stmt, env),
        //// identifier
        Node::Identifier(ident) => eval_identifier(ident, env),
        //// literals
        Node::IntegerLiteral(int_literal) => Ok(object::Object::Integer(object::Integer::new(
            int_literal.value,
        ))),
        Node::BoolLiteral(bool_literal) => {
            Ok(object::Object::Bool(object::Bool::new(bool_literal.value)))
        }
        _ => unimplemented!(),
    }
}

fn eval_program(program: &ast::Program, env: &mut Environment) -> Result<object::Object> {
    let stmts = &program.statements;

    if stmts.is_empty() {
        return Err(anyhow!("statements is empty."));
    }

    for (i, stmt) in stmts.iter().enumerate() {
        let result = eval(stmt, env).context("failed to evaluate a statement.")?;

        if let Object::ReturnValue(ret_value) = result {
            return Ok((*ret_value.value).clone());
        }

        if i == stmts.len() - 1 {
            return Ok(result);
        }
    }

    unreachable!()
}

fn eval_block_statement(
    block_stmt: &ast::BlockStatement,
    env: &mut Environment,
) -> Result<object::Object> {
    let stmts = &block_stmt.statements;

    if stmts.is_empty() {
        return Err(anyhow!("statements is empty."));
    }

    for (i, stmt) in stmts.iter().enumerate() {
        let result = eval(stmt, env).context("failed to evaluate a statement.")?;

        if i == stmts.len() - 1 || result.is_returned() {
            return Ok(result);
        }
    }

    unreachable!()
}

fn eval_statements(statements: &[ast::Statement], env: &mut Environment) -> Result<object::Object> {
    if statements.is_empty() {
        return Err(anyhow!("statements is empty."));
    }

    for (i, stmt) in statements.iter().enumerate() {
        let result = eval(stmt, env).context("failed to evaluate a statement.")?;

        if let Object::ReturnValue(ret_value) = result {
            return Ok((*ret_value.value).clone());
        }

        if i == statements.len() - 1 {
            return Ok(result);
        }
    }

    unreachable!()
}

// prefix
fn eval_prefix_expression(
    operator: &[ascii::Char],
    right: &object::Object,
) -> Result<object::Object> {
    match operator.as_str() {
        "!" => Ok(eval_exclamation_operator_expression(right)),
        "-" => Ok(eval_minus_prefix_operator_expression(right)
            .context("failed to eval minux prefix operator expression.")?),
        _ => bail!("unknown operator: {}", operator.as_str()),
    }
}

fn eval_exclamation_operator_expression(right: &object::Object) -> object::Object {
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

fn eval_minus_prefix_operator_expression(right: &object::Object) -> Result<object::Object> {
    if let object::Object::Integer(int_obj) = right {
        return Ok(object::Object::Integer(object::Integer::new(
            -int_obj.value,
        )));
    }

    bail!("minus is not prefix operator for {}.", right);
}

// infix
fn eval_infix_expression(
    operator: &[ascii::Char],
    left: &object::Object,
    right: &object::Object,
) -> Result<object::Object> {
    // 型が違う場合はエラー
    if discriminant(left) != discriminant(right) {
        bail!("type mismatch: {left:?} {} {right:?}", operator.as_str());
    }

    match operator.as_str() {
        "==" => Ok(object::Object::Bool(object::Bool::new(*right == *left))),
        "!=" => Ok(object::Object::Bool(object::Bool::new(*right != *left))),
        _ => {
            if let (object::Object::Integer(x), object::Object::Integer(y)) = (left, right) {
                return eval_integer_infix_expression(operator, x, y)
                    .context("failed to eval infix expression for integers.");
            }

            bail!("unknown operator: {}", operator.as_str());
        }
    }
}

fn eval_integer_infix_expression(
    operator: &[ascii::Char],
    left: &object::Integer,
    right: &object::Integer,
) -> Result<object::Object> {
    match operator.as_str() {
        "+" => Ok(object::Object::int(left.value + right.value)),
        "-" => Ok(object::Object::int(left.value - right.value)),
        "*" => Ok(object::Object::int(left.value * right.value)),
        "/" => Ok(object::Object::int(left.value / right.value)),
        "<" => Ok(object::Object::bool(left.value < right.value)),
        ">" => Ok(object::Object::bool(left.value > right.value)),
        "==" => Ok(object::Object::bool(left.value == right.value)),
        "!=" => Ok(object::Object::bool(left.value != right.value)),
        _ => bail!("unknown operator: {}.", operator.as_str()),
    }
}

// if-else
fn eval_if_expression(if_expr: &ast::IfExpression, env: &mut Environment) -> Result<Object> {
    let cond_obj =
        eval(&*if_expr.condition, env).context("failed to eval expression for condition.")?;

    if is_truethy(&cond_obj) {
        eval(&if_expr.consequence, env).context("failed to eval consequence block.")
    } else if let Some(alt) = &if_expr.alternative {
        eval(alt, env).context("failed to eval alternative block.")
    } else {
        Ok(NULL.clone())
    }
}

fn is_truethy(obj: &object::Object) -> bool {
    match obj {
        Object::Bool(b) => b.value,
        Object::Null(_) => false,
        _ => true,
    }
}

// let
fn eval_identifier(ident: &ast::Identifier, env: &Environment) -> Result<Object> {
    if let Some(value) = env.get(ident.value.as_str()) {
        return Ok(value.clone());
    }

    bail!("identifier not found: {}", ident.value.as_str());
}

mod test {
    use std::ascii;
    use std::sync::BarrierWaitResult;

    use anyhow::{Result, anyhow, bail};

    use crate::lexer::Lexer;
    use crate::object::{self, Environment, Object};
    use crate::parser::Parser;
    use crate::utils::print_errors;

    use super::eval;

    #[test]
    fn test_eval_integer_expression() {
        #[derive(Debug)]
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
            let obj = test_eval(&test.input);
            test_integer_object(&obj, test.expected).unwrap_or_else(|err| {
                panic!("test {i} failed: {}", err);
            });
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

        for test in tests.iter() {
            let obj = test_eval(&test.input);
            test_bool_object(&obj, test.expected);
        }
    }

    #[test]
    fn test_eval_exclamation_operator() {
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

    #[test]
    fn test_if_else_expressoin() {
        #[derive(Debug)]
        struct Test {
            input: Vec<ascii::Char>,
            expected: Object,
        }
        impl Test {
            fn new(input: &str, expected: Object) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    expected,
                }
            }
        }

        let tests = vec![
            Test::new("if (true) { 10 }", object::Object::int(10)),
            Test::new("if (false) { 10 }", object::Object::null()),
            Test::new("if (1) { 10 }", object::Object::int(10)),
            Test::new("if (1 < 2) { 10 }", object::Object::int(10)),
            Test::new("if (1 > 2) { 10 }", object::Object::null()),
            Test::new("if (1 > 2) { 10 } else { 20 }", object::Object::int(20)),
            Test::new("if (1 < 2) { 10 } else { 20 }", object::Object::int(10)),
        ];

        for (i, test) in tests.iter().enumerate() {
            let obj = test_eval(&test.input);

            let r = match &test.expected {
                object::Object::Bool(b) => test_bool_object(&obj, b.value),
                object::Object::Integer(i) => test_integer_object(&obj, i.value),
                object::Object::Null(n) => test_null_object(&obj),
                object::Object::ReturnValue(_) => panic!("program returned ReturnValue."),
            };

            r.unwrap_or_else(|err| {
                panic!("test {} failed. got: {}", i, err);
            });
        }
    }

    #[test]
    fn test_return_statement() {
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
            let obj = test_eval(&test.input);
            test_integer_object(&obj, test.expected).unwrap_or_else(|err| {
                panic!("test {} failed: {}", i, err);
            });
        }
    }

    #[test]
    fn test_let_statements() {
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

        let tests = vec![
            Test::new("let a = 5; a;", 5),
            Test::new("let a = 5 * 5; a;", 25),
            Test::new("let a = 5; let b = a; b;", 5),
            Test::new("let a = 5; let b = a; let c = a + b + 5; c;", 15),
        ];

        for (i, test) in tests.iter().enumerate() {
            let obj = test_eval(&test.input);
            test_integer_object(&obj, test.expected).unwrap_or_else(|err| {
                panic!("test {i} failed: {err}.",);
            });
        }
    }

    fn test_eval(input: &[ascii::Char]) -> object::Object {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program().unwrap_or_else(|_| {
            parser.print_errors();
            panic!("failed to parse.");
        });
        let mut env = Environment::new();

        eval(&program, &mut env).unwrap_or_else(|e| {
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

        if int_obj.value != expected {
            bail!("int_obj.value is not {expected}. got: {}", int_obj.value);
        }

        Ok(())
    }

    fn test_bool_object(obj: &Object, expected: bool) -> Result<()> {
        let bool_obj = if let Object::Bool(bool_obj) = obj {
            bool_obj
        } else {
            bail!("obj is not Bool. got: {obj:?}");
        };

        if bool_obj.value != expected {
            bail!("bool_obj.value is not {expected}. got: {}", bool_obj.value);
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
