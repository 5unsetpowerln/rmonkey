use std::rc::Rc;

use anyhow::{Context, Result, bail};
use thiserror::Error;

use crate::code::{OpCodeKind, create_inst};
use crate::{ast, object};

#[derive(Debug, Error)]
pub enum CompileError {
    #[error("unknown operator `{operator}`")]
    UnknownOperator { operator: String },
}

#[derive(Debug)]
pub struct ByteCode {
    pub instructions: Vec<u8>,
    pub constants: Vec<Rc<object::Object>>,
}

impl ByteCode {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            constants: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub struct Compiler {
    bytecode: ByteCode,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            bytecode: ByteCode::new(),
        }
    }

    fn add_inst(&mut self, kind: OpCodeKind, operands: &[i64]) -> Result<()> {
        self.bytecode.instructions.extend_from_slice(
            create_inst(kind, operands)
                .context("failed to create an instruction")?
                .as_ref(),
        );

        Ok(())
    }

    /// 定数を定数リストに追加し、追加された定数のインデックスを返す
    fn add_const(&mut self, obj: Rc<object::Object>) -> usize {
        self.bytecode.constants.push(obj);
        self.bytecode.constants.len() - 1
    }

    pub fn compile<T: ast::NodeInterface>(&mut self, node: &T) -> Result<()> {
        match node.get_node() {
            ast::Node::Program(program) => {
                for stmt in program.statements.iter() {
                    self.compile(stmt).context("failed to parse a statement.")?;
                }
            }

            ast::Node::Statement(stmt) => match stmt {
                ast::Statement::Expression(expr_stmt) => self
                    .compile(expr_stmt)
                    .context("failed to compile the expression statement.")?,
                ast::Statement::Let(let_stmt) => self
                    .compile(let_stmt)
                    .context("failed to compile the let statement.")?,
                ast::Statement::Return(ret_stmt) => self
                    .compile(ret_stmt)
                    .context("failed to compile the return statement.")?,
            },

            ast::Node::ExpressionStatement(expr_stmt) => {
                self.compile(&expr_stmt.value)
                    .context("failed to compile the expression.")?;
                self.add_inst(OpCodeKind::Pop, &[])
                    .context("failed to add the pop instruction.")?;
            }

            ast::Node::Expression(expr) => match expr {
                ast::Expression::ArrayLiteral(x) => self
                    .compile(x)
                    .context("failed to compile the array literal.")?,
                ast::Expression::Identifier(x) => self
                    .compile(x)
                    .context("failed to compile the identifier.")?,
                ast::Expression::BlockStatement(x) => self
                    .compile(x)
                    .context("failed to compile the block statement.")?,
                ast::Expression::Infix(x) => self
                    .compile(x)
                    .context("failed to compile the infix expression.")?,
                ast::Expression::Prefix(x) => self
                    .compile(x)
                    .context("failed to compile the prefix expression.")?,
                ast::Expression::BoolLiteral(x) => self
                    .compile(x)
                    .context("failed to compile the bool literal.")?,
                ast::Expression::If(x) => self
                    .compile(x)
                    .context("failed to compile the if expression.")?,
                ast::Expression::Function(x) => self
                    .compile(x)
                    .context("failed to compile the function literal.")?,
                ast::Expression::Call(x) => self
                    .compile(x)
                    .context("failed to compile the call expression.")?,
                ast::Expression::StringLiteral(x) => self
                    .compile(x)
                    .context("failed to compile the string literal.")?,
                ast::Expression::IndexExpression(x) => self
                    .compile(x)
                    .context("failed to compile the index expression.")?,
                ast::Expression::HashLiteral(x) => self
                    .compile(x)
                    .context("failed to compile the hash literal.")?,
                ast::Expression::IntegerLiteral(x) => self
                    .compile(x)
                    .context("failed to compile the integer literal.")?,
            },

            ast::Node::InfixExpression(infix_expr) => {
                self.compile(infix_expr.left.as_ref())
                    .context("failed to compile the left expression.")?;
                self.compile(infix_expr.right.as_ref())
                    .context("failed to compile the right expression.")?;

                match infix_expr.operator.as_str() {
                    "+" => self
                        .add_inst(OpCodeKind::Add, &[])
                        .context("failed to add the add instruction")?,
                    _ => bail!(CompileError::UnknownOperator {
                        operator: infix_expr.operator.clone()
                    }),
                };
            }

            ast::Node::IntegerLiteral(int_literal) => {
                let int_obj = object::Object::int(int_literal.value);

                let idx = self.add_const(Rc::new(int_obj));
                let operands = [idx as i64];

                self.add_inst(OpCodeKind::Constant, &operands)
                    .context("failed to add the constant instuction.")?;
            }

            _ => unimplemented!(),
        }

        Ok(())
    }

    pub fn get_bytecode(&self) -> &ByteCode {
        &self.bytecode
    }
}

mod test {
    use std::rc::Rc;

    use anyhow::{Context, Result, bail};

    use crate::ast::Program;
    use crate::code::{OpCodeKind, create_inst, insts_from_inst_list};
    use crate::compiler::Compiler;
    use crate::disasm::disasm;
    use crate::lexer::Lexer;
    use crate::object::Object;
    use crate::parser::Parser;
    use crate::utils::print_errors;

    struct CompilerTestCase {
        input: String,
        expected_consts: Vec<Object>,
        expected_insts: Vec<u8>,
    }

    impl CompilerTestCase {
        fn new(input: &str, expected_consts: &[Object], expected_inst_list: &[Vec<u8>]) -> Self {
            let expected_insts = insts_from_inst_list(expected_inst_list);

            Self {
                input: input.to_string(),
                expected_consts: expected_consts.to_vec(),
                expected_insts,
            }
        }
    }

    fn run_compiler_tests(tests: &[CompilerTestCase]) {
        for (i, test) in tests.iter().enumerate() {
            let program = parse(&test.input).unwrap_or_else(|err| {
                print_errors(
                    &format!("test {} failed. failed to parse a program.", i),
                    err,
                );
                panic!()
            });

            let mut compiler = Compiler::new();
            compiler.compile(&program).unwrap_or_else(|err| {
                print_errors(
                    &format!("test {} failed. failed to compile a program.", i),
                    err,
                );
                panic!();
            });

            let bytecode = compiler.get_bytecode();

            test_insts(&test.expected_insts, &bytecode.instructions).unwrap_or_else(|err| {
                print_errors(
                    &format!("test {} failed. failed to test instructions.", i),
                    err,
                );
                panic!();
            });

            test_consts(&test.expected_consts, &bytecode.constants).unwrap_or_else(|err| {
                print_errors(
                    &format!("test {} failed. failed to test constants.", i),
                    err,
                );
                panic!();
            });
        }
    }

    fn parse(input: &str) -> Result<Program> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        parser.parse_program()
    }

    fn test_insts(expected: &[u8], actual: &[u8]) -> Result<()> {
        if expected.len() != actual.len() {
            bail!(
                "wrong instructions length.\nexpected:\n{}got:\n{}",
                expected.len(),
                actual.len(),
            );
        }

        for (i, expected_byte) in expected.iter().enumerate() {
            if actual[i] != *expected_byte {
                bail!(
                    "wrong byte at {}. expected: {}, got: {}.\nexpected:\n{}got:\n{}",
                    i,
                    expected_byte,
                    actual[i],
                    disasm(expected),
                    disasm(actual),
                );
            }
        }

        Ok(())
    }

    fn test_consts(expected: &[Object], actual: &[Rc<Object>]) -> Result<()> {
        if expected.len() != actual.len() {
            bail!(
                "wrong number of constants. expected: {}, got: {}.",
                expected.len(),
                actual.len(),
            );
        }

        for (i, expected_const) in expected.iter().enumerate() {
            match expected_const {
                Object::Integer(int_obj) => {
                    test_integer_object(int_obj.borrow().value, &actual[i])
                        .with_context(|| format!("constant {} failed", i))?;
                }
                _ => unimplemented!(),
            }
        }

        Ok(())
    }

    fn test_integer_object(expected: i64, actual: &Object) -> Result<()> {
        match actual {
            Object::Integer(integer_object) => {
                if integer_object.borrow().value != expected {
                    bail!(
                        "object has wrong value. expected: {}, got: {}.",
                        expected,
                        integer_object.borrow().value
                    );
                }
            }
            other => {
                bail!("object is not Integer. got: {}", other)
            }
        }

        Ok(())
    }

    #[test]
    fn test_integer_arithmetic() {
        let tests = [
            CompilerTestCase::new(
                "1 + 2",
                &[Object::int(1), Object::int(2)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::Add, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "1; 2",
                &[Object::int(1), Object::int(2)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
        ];

        run_compiler_tests(&tests);
    }
}
