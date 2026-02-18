use core::ascii;
use std::cell::RefCell;
use std::mem::discriminant;
use std::rc::Rc;

use anyhow::{Context, Result, anyhow, bail, ensure};

use crate::ast::{Node, NodeInterface};
use crate::object::{Environment, Object, create_false, create_null, create_true};
use crate::{ast, builtins, object};

pub fn eval<T: ast::NodeInterface>(
    node: &T,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<object::Object>> {
    env.borrow_mut()
        .set("len", Rc::new(Object::builtin(builtins::len)));
    env.borrow_mut()
        .set("first", Rc::new(Object::builtin(builtins::first)));
    env.borrow_mut()
        .set("last", Rc::new(Object::builtin(builtins::last)));
    env.borrow_mut()
        .set("push", Rc::new(Object::builtin(builtins::push)));

    __eval(node, env)
}

fn __eval<T: ast::NodeInterface>(
    node: &T,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<object::Object>> {
    match node.get_node() {
        // program
        Node::Program(program) => eval_program(program, env),
        // statements
        Node::Statement(stmt) => match stmt {
            ast::Statement::Expression(x) => __eval(x, env),
            ast::Statement::Let(x) => __eval(x, env),
            ast::Statement::Return(x) => __eval(x, env),
        },
        Node::ExpressionStatement(expr_stmt) => __eval(&expr_stmt.value, env),
        Node::ReturnStatement(ret_stmt) => {
            let value = __eval(&ret_stmt.value, env)
                .context("failed to eval expression for return value.")?;
            Ok(Rc::new(Object::ret_val(value)))
        }
        Node::LetStatement(let_stmt) => {
            let value = __eval(&let_stmt.value, env.clone())
                .context("failed to eval value for let statement.")
                .context("failed to eval let statement.")?;
            env.borrow_mut().set(let_stmt.name.value.as_str(), value);
            Ok(create_null())
        }
        // expressions
        //// general expressions
        Node::Expression(expr) => match expr {
            ast::Expression::BoolLiteral(x) => __eval(x, env),
            ast::Expression::Call(x) => __eval(x, env),
            ast::Expression::Function(x) => __eval(x, env),
            ast::Expression::Identifier(x) => __eval(x, env),
            ast::Expression::If(x) => __eval(x, env),
            ast::Expression::Infix(x) => __eval(x, env),
            ast::Expression::IntegerLiteral(x) => __eval(x, env),
            ast::Expression::Prefix(x) => __eval(x, env),
            ast::Expression::StringLiteral(x) => __eval(x, env),
            ast::Expression::ArrayLiteral(x) => __eval(x, env),
            ast::Expression::IndexExpression(x) => __eval(x, env),
        },
        //// prefix expression
        Node::PrefixExpression(prefix_expr) => {
            let right = __eval(&*prefix_expr.right, env)
                .context("failed to eval right expression")
                .context("failed to eval prefix expression")?;

            eval_prefix_expression(&prefix_expr.operator, &right)
                .context("failed to eval prefix expression")
        }
        //// infix expression
        Node::InfixExpression(infix_expr) => {
            let left = __eval(&*infix_expr.left, env.clone())
                .context("failed to eval left expression")
                .context("failed to eval infix expression")?;
            let right = __eval(&*infix_expr.right, env)
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
        //// function call
        Node::CallExpression(call_expr) => {
            let func = __eval(&*call_expr.func, env.clone())
                .context("failed to get function.")
                .context("failed to eval call expression.")?;

            let args = eval_expressions(&call_expr.args, env)
                .context("failed to eval arguments.")
                .context("failed to eval call expression.")?;

            apply_function(func, &args)
                .context("failed to apply function?")
                .context("failed to eval call expression.")
        }
        //// index reference
        Node::IndexExpression(idx_expr) => {
            let left = __eval(&*idx_expr.left, env.clone())
                .context("failed to eval left object.")
                .context("failed to eval index expression.")?;
            let index = __eval(&*idx_expr.index, env)
                .context("failed to index object.")
                .context("failed to eval index expression.")?;

            eval_index_expression(left, index).context("failed to eval index expression.")
        }

        //// literals
        Node::IntegerLiteral(int_literal) => Ok(Rc::new(Object::int(int_literal.value))),
        Node::BoolLiteral(bool_literal) => Ok(Rc::new(Object::bool(bool_literal.value))),
        Node::FunctionLiteral(func_literal) => {
            Ok(Rc::new(Object::from_func_litereal(func_literal, env)))
        }
        Node::StringLiteral(literal) => Ok(Rc::new(Object::str(&literal.value))),
        Node::ArrayLiteral(literal) => {
            let elements = eval_expressions(&literal.elements, env)
                .context("failed to eval elements")
                .context("failed to eval array literal.")?;
            Ok(Rc::new(Object::Array(Rc::new(RefCell::new(
                object::Array::new(&elements),
            )))))
        }
        _ => unimplemented!(),
    }
}

fn eval_program(
    program: &ast::Program,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<object::Object>> {
    let stmts = &program.statements;

    if stmts.is_empty() {
        return Err(anyhow!("statements is empty."));
    }

    for (i, stmt) in stmts.iter().enumerate() {
        let result = __eval(stmt, env.clone()).context("failed to evaluate a statement.")?;

        if let Object::ReturnValue(ret_value) = &*result {
            return Ok(ret_value.borrow().value.clone());
        }

        if i == stmts.len() - 1 {
            return Ok(result);
        }
    }

    unreachable!()
}

fn eval_block_statement(
    block_stmt: &ast::BlockStatement,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let stmts = &block_stmt.statements;

    if stmts.is_empty() {
        return Err(anyhow!("statements is empty."));
    }

    for (i, stmt) in stmts.iter().enumerate() {
        let result = __eval(stmt, env.clone()).context("failed to evaluate a statement.")?;

        if i == stmts.len() - 1 || result.is_returned() {
            return Ok(result);
        }
    }

    unreachable!()
}

fn eval_statements(
    statements: &[ast::Statement],
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    if statements.is_empty() {
        return Err(anyhow!("statements is empty."));
    }

    for (i, stmt) in statements.iter().enumerate() {
        let result = __eval(stmt, env.clone()).context("failed to evaluate a statement.")?;

        if let Object::ReturnValue(ret_value) = &*result {
            return Ok(ret_value.borrow().value.clone());
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
) -> Result<Rc<object::Object>> {
    match operator.as_str() {
        "!" => Ok(eval_exclamation_operator_expression(right)),
        "-" => Ok(eval_minus_prefix_operator_expression(right)
            .context("failed to eval minux prefix operator expression.")?),
        _ => bail!("unknown operator: {}", operator.as_str()),
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

    bail!("minus is not prefix operator for {}.", right);
}

// infix
fn eval_infix_expression(
    operator: &[ascii::Char],
    left: &object::Object,
    right: &object::Object,
) -> Result<Rc<object::Object>> {
    // 型が違う場合はエラー
    if discriminant(left) != discriminant(right) {
        bail!("type mismatch: {left:?} {} {right:?}", operator.as_str());
    }

    match operator.as_str() {
        "==" => Ok(Rc::new(Object::bool(*right == *left))),
        "!=" => Ok(Rc::new(Object::bool(*right != *left))),
        _ => {
            if let (object::Object::Integer(x), object::Object::Integer(y)) = (left, right) {
                return eval_integer_infix_expression(operator, &*x.borrow(), &*y.borrow())
                    .context("failed to eval infix expression for integers.");
            }

            if let (Object::String(x), Object::String(y)) = (left, right) {
                return eval_string_infix_expression(operator, &*x.borrow(), &*y.borrow())
                    .context("failed to eval infix expression for string.");
            }

            bail!("unknown operator: {}", operator.as_str());
        }
    }
}

fn eval_integer_infix_expression(
    operator: &[ascii::Char],
    left: &object::Integer,
    right: &object::Integer,
) -> Result<Rc<object::Object>> {
    match operator.as_str() {
        "+" => Ok(Rc::new(Object::int(left.value + right.value))),
        "-" => Ok(Rc::new(Object::int(left.value - right.value))),
        "*" => Ok(Rc::new(Object::int(left.value * right.value))),
        "/" => Ok(Rc::new(Object::int(left.value / right.value))),
        "<" => Ok(Rc::new(Object::bool(left.value < right.value))),
        ">" => Ok(Rc::new(Object::bool(left.value > right.value))),
        "==" => Ok(Rc::new(Object::bool(left.value == right.value))),
        "!=" => Ok(Rc::new(Object::bool(left.value != right.value))),
        _ => bail!("unknown operator: {}.", operator.as_str()),
    }
}

fn eval_string_infix_expression(
    operator: &[ascii::Char],
    left: &object::StringObject,
    right: &object::StringObject,
) -> Result<Rc<Object>> {
    ensure!(
        operator.as_str() == "+",
        "unknown operator: {}",
        operator.as_str()
    );

    Ok(Rc::new(Object::str(
        format!("{}{}", left.value.as_str(), right.value.as_str())
            .as_ascii()
            .unwrap(),
    )))
}

// if-else
fn eval_if_expression(
    if_expr: &ast::IfExpression,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let cond_obj = __eval(&*if_expr.condition, env.clone())
        .context("failed to eval expression for condition.")?;

    if is_truethy(cond_obj) {
        __eval(&if_expr.consequence, env).context("failed to eval consequence block.")
    } else if let Some(alt) = &if_expr.alternative {
        __eval(alt, env.clone()).context("failed to eval alternative block.")
    } else {
        Ok(create_null())
    }
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

    bail!("identifier not found: {}", ident.value.as_str());
}

// index expression
fn eval_index_expression(left: Rc<Object>, index: Rc<Object>) -> Result<Rc<Object>> {
    match (&*left, &*index) {
        (Object::Array(array), Object::Integer(integer)) => {
            let obj = if let Some(obj) = array.borrow().array.get(integer.borrow().value as usize) {
                obj.clone()
            } else {
                Rc::new(Object::null())
            };

            Ok(obj)
        }
        _ => Err(anyhow!(
            "unsupported pattern of left and index object. left object: {:?}, index object: {:?}",
            &*left,
            &*index
        )),
    }
}

//
fn eval_expressions(
    expressions: &[ast::Expression],
    env: Rc<RefCell<Environment>>,
) -> Result<Vec<Rc<Object>>> {
    let mut objs = Vec::new();

    for (i, expr) in expressions.iter().enumerate() {
        let evaluated =
            __eval(expr, env.clone()).with_context(|| format!("failed to eval expression {i}"))?;

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
                .context("failed to create environment for function")?;

            let evaluated = __eval(&func.borrow().body, func_env)
                .context("failed to eval body of function.")?;

            Ok(unwrap_return_value(evaluated))
        }
        Object::Builtin(builtin) => {
            (builtin.borrow().func)(args).context("failed to run builtin function.")
        }
        _ => Err(anyhow!("not a function: {f:?}")),
    }
}

fn unwrap_return_value(obj: Rc<Object>) -> Rc<Object> {
    match &*obj {
        Object::ReturnValue(r) => r.borrow().value.clone(),
        _ => obj,
    }
}

mod test {
    use std::ascii;
    use std::cell::RefCell;
    use std::rc::Rc;

    use anyhow::{Result, bail};

    use crate::ast::NodeInterface;
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

    #[test]
    fn test_function_object() {
        let input = "fn(x) { x + 2; };".as_ascii().unwrap();

        let evaluated = &*test_eval(input);

        let fn_obj = if let Object::Function(x) = evaluated {
            x
        } else {
            panic!("object is not Function. got: {evaluated:?}");
        };

        if fn_obj.borrow().params.len() != 1 {
            panic!("number of parameter for function is wrong.");
        }

        if fn_obj.borrow().params[0].string().as_str() != "x" {
            panic!("parameter is not 'x'");
        }

        let expected_body = "(x + 2)";

        if fn_obj.borrow().body.string().as_str() != expected_body {
            panic!("body is not {expected_body}. got: {}", fn_obj.borrow());
        }
    }

    #[test]
    fn test_function_application() {
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
            Test::new("let identity = fn(x) { x; }; identity(5);", 5),
            Test::new("let identity = fn(x) { return x; }; identity(5);", 5),
            Test::new("let double = fn(x) { x * 2; }; double(5);", 10),
            Test::new("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
            Test::new("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
            Test::new("fn(x) { x; }(5)", 5),
        ];

        for (i, test) in tests.iter().enumerate() {
            test_integer_object(&test_eval(&test.input), test.expected).unwrap_or_else(|err| {
                print_errors("test {i} failed", err);
                panic!();
            });
        }
    }

    #[test]
    fn test_closures() {
        let input = "
            let newAdder = fn(x) {
              fn(y) { x + y };
            };

            let addTwo = newAdder(2);
            addTwo(2);
            "
        .as_ascii()
        .unwrap();

        test_integer_object(&*test_eval(input), 4).unwrap_or_else(|err| {
            print_errors("test failed.", err);
            panic!()
        });
    }

    #[test]
    fn test_string_literal() {
        let input = "\"Hello World!\"".as_ascii().unwrap();

        let evaluated = &*test_eval(input);

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
        let input = "\"Hello\" + \" \" + \"World!\"".as_ascii().unwrap();

        let evaluated = &*test_eval(input);

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
            Test::new("len(\"\")", 0),
            Test::new("len(\"four\")", 4),
            Test::new("len(\"hello world\")", 11),
        ];

        for (i, test) in tests.iter().enumerate() {
            let evaluated = &*test_eval(&test.input);

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
        let input = "[1, 2 * 2, 3 + 3]".as_ascii().unwrap();

        let evaluated = &*test_eval(input);

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
            Test::new("[1, 2, 3][0]", Object::int(1)),
            Test::new("[1, 2, 3][1]", Object::int(2)),
            Test::new("[1, 2, 3][2]", Object::int(3)),
            Test::new("let i = 0; [1][i];", Object::int(1)),
            Test::new("[1, 2, 3][1 + 1];", Object::int(3)),
            Test::new("let myArray = [1, 2, 3]; myArray[2];", Object::int(3)),
            Test::new(
                "let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2];",
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
            let evaluated = &*test_eval(&test.input);

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

    fn test_eval(input: &[ascii::Char]) -> Rc<object::Object> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program().unwrap_or_else(|_| {
            parser.print_errors();
            panic!("failed to parse.");
        });

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
