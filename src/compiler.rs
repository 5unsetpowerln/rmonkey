use std::rc::Rc;

use anyhow::{Context, Result};

use crate::code::{Instruction, Instructions, OpCodeKind};
use crate::{ast, object};

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

    /// 命令を追加し、追加された命令のオフセットを返す
    fn add_instruction(&mut self, inst: &Instruction) -> usize {
        let new_inst_pos = self.bytecode.instructions.len();
        self.bytecode.instructions.add_inst(inst);
        new_inst_pos
    }

    /// 定数を定数リストに追加し、追加された定数のインデックスを返す
    fn add_constant(&mut self, obj: Rc<object::Object>) -> usize {
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

            ast::Node::ExpressionStatement(expr_stmt) => self
                .compile(&expr_stmt.value)
                .context("failed to compile the expression.")?,

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
            }

            ast::Node::IntegerLiteral(int_literal) => {
                let int_obj = object::Object::int(int_literal.value);

                let operands = &[self.add_constant(Rc::new(int_obj)) as u64];

                self.add_instruction(
                    &Instruction::new(OpCodeKind::Constant, operands)
                        .context("failed to create the constant instruction.")?,
                );
            }

            _ => unimplemented!(),
        }

        Ok(())
    }

    pub fn get_bytecode(&self) -> &ByteCode {
        &self.bytecode
    }
}

#[derive(Debug)]
pub struct ByteCode {
    pub instructions: Instructions,
    pub constants: Vec<Rc<object::Object>>,
}

impl ByteCode {
    pub fn new() -> Self {
        Self {
            instructions: Instructions::new(),
            constants: Vec::new(),
        }
    }
}

mod test {
    use std::rc::Rc;

    use anyhow::{Context, Result, bail};

    use crate::ast::Program;
    use crate::code::{Instruction, Instructions, OpCodeKind};
    use crate::compiler::Compiler;
    use crate::lexer::Lexer;
    use crate::object::Object;
    use crate::parser::Parser;
    use crate::utils::print_errors;

    struct CompilerTestCase {
        input: String,
        expected_constants: Vec<Object>,
        expected_instructions: Instructions,
    }

    impl CompilerTestCase {
        fn new(
            input: &str,
            expected_constants: &[Object],
            expected_instructions: &[Instructions],
        ) -> Self {
            let expected_instructions = Instructions::merge(expected_instructions);

            Self {
                input: input.to_string(),
                expected_constants: expected_constants.to_vec(),
                expected_instructions,
            }
        }
    }

    /// Instruction から Instructions を作るヘルパー
    fn make_insts(kind: OpCodeKind, operands: &[u64]) -> Instructions {
        let inst = Instruction::new(kind, operands).unwrap();
        let mut insts = Instructions::new();
        insts.add_inst(&inst);
        insts
    }

    #[test]
    fn test_integer_arithmetic() {
        let tests = [CompilerTestCase::new(
            "1 + 2",
            &[Object::int(1), Object::int(2)],
            &[
                make_insts(OpCodeKind::Constant, &[0]),
                make_insts(OpCodeKind::Constant, &[1]),
            ],
        )];

        run_compiler_tests(&tests);
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

            test_insts(&test.expected_instructions, &bytecode.instructions).unwrap_or_else(|err| {
                print_errors(
                    &format!("test {} failed. failed to test instructions.", i),
                    err,
                );
                panic!();
            });

            test_consts(&test.expected_constants, &bytecode.constants).unwrap_or_else(|err| {
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

    fn test_insts(expected: &Instructions, actual: &Instructions) -> Result<()> {
        if expected.len() != actual.len() {
            bail!(
                "wrong instructions length.\nexpected:\n{}got:\n{}",
                expected,
                actual,
            );
        }

        for (i, expected_byte) in expected.iter().enumerate() {
            if actual[i] != *expected_byte {
                bail!(
                    "wrong byte at {}. expected: {}, got: {}.\nexpected:\n{}got:\n{}",
                    i,
                    expected_byte,
                    actual[i],
                    expected,
                    actual,
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
}
