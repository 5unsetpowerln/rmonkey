use std::mem;
use std::sync::Arc;

use anyhow::{Context, Result, bail};
use thiserror::Error;

use crate::ast::{BlockStatement, PrefixExpression};
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
    pub constants: Vec<Arc<object::Object>>,
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
    last_inst: Option<AddedInstruction>, // 最近追加された命令
    prev_inst: Option<AddedInstruction>, // その前に追加された命令
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            bytecode: ByteCode::new(),
            last_inst: None,
            prev_inst: None,
        }
    }

    fn add_inst(&mut self, kind: OpCodeKind, operands: &[i64]) -> Result<usize> {
        let position = self.bytecode.instructions.len();

        self.bytecode.instructions.extend_from_slice(
            create_inst(kind, operands)
                .context("failed to create an instruction")?
                .as_ref(),
        );

        self.set_last_inst(kind, position);

        Ok(position)
    }

    fn set_last_inst(&mut self, kind: OpCodeKind, position: usize) {
        mem::swap(&mut self.last_inst, &mut self.prev_inst);
        self.last_inst = Some(AddedInstruction::new(kind, position));
    }

    fn last_inst_is(&self, kind: OpCodeKind) -> bool {
        matches!(&self.last_inst, Some(kind))
    }

    fn remove_last_inst(&mut self) {
        self.bytecode
            .instructions
            .truncate(self.last_inst.as_ref().unwrap().position);
        mem::swap(&mut self.last_inst, &mut self.prev_inst);
        self.prev_inst = None;
    }

    fn replace_inst(&mut self, position: usize, inst: &[u8]) {
        self.bytecode
            .instructions
            .get_mut(position..position + inst.len())
            .unwrap()
            .copy_from_slice(inst);
    }

    fn change_operands(&mut self, position: usize, operands: &[i64]) -> Result<()> {
        let kind = OpCodeKind::from_u8(self.bytecode.instructions[position])
            .context("failed to parse a byte as OpCodeKind.")?;
        let new_inst = create_inst(kind, operands).context("failed to create new instruction.")?;
        self.replace_inst(position, new_inst.as_ref());
        Ok(())
    }

    /// 定数を定数リストに追加し、追加された定数のインデックスを返す
    fn add_const(&mut self, obj: Arc<object::Object>) -> usize {
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

            ast::Node::PrefixExpression(prefix_expr) => {
                self.compile(prefix_expr.right.as_ref())
                    .context("failed to compile the left expression.")?;

                match prefix_expr.operator.as_str() {
                    "-" => self
                        .add_inst(OpCodeKind::Minus, &[])
                        .context("failed to compile the minus operator.")?,
                    "!" => self
                        .add_inst(OpCodeKind::Bang, &[])
                        .context("failed to compile the bang operator.")?,
                    _ => bail!(CompileError::UnknownOperator {
                        operator: prefix_expr.operator.clone()
                    }),
                };
            }

            ast::Node::InfixExpression(infix_expr) => {
                if infix_expr.operator.as_str() == "<" {
                    self.compile(infix_expr.right.as_ref())
                        .context("failed to compile the right expression.")?;
                    self.compile(infix_expr.left.as_ref())
                        .context("failed to compile the left expression.")?;
                    self.add_inst(OpCodeKind::GreaterThan, &[])
                        .context("failed to add the greater-than instruction.")?;
                    return Ok(());
                }

                self.compile(infix_expr.left.as_ref())
                    .context("failed to compile the left expression.")?;
                self.compile(infix_expr.right.as_ref())
                    .context("failed to compile the right expression.")?;

                match infix_expr.operator.as_str() {
                    "+" => self
                        .add_inst(OpCodeKind::Add, &[])
                        .context("failed to add the add instruction")?,
                    "-" => self
                        .add_inst(OpCodeKind::Sub, &[])
                        .context("failed to add the sub instruction")?,
                    "*" => self
                        .add_inst(OpCodeKind::Mul, &[])
                        .context("failed to add the mul instruction")?,
                    "/" => self
                        .add_inst(OpCodeKind::Div, &[])
                        .context("failed to add the div instruction")?,
                    "==" => self
                        .add_inst(OpCodeKind::Equal, &[])
                        .context("failed to add the equal instruction.")?,
                    "!=" => self
                        .add_inst(OpCodeKind::NotEqual, &[])
                        .context("failed to add the not-equal instruction.")?,
                    ">" => self
                        .add_inst(OpCodeKind::GreaterThan, &[])
                        .context("failed to add the greater-than instruction.")?,
                    _ => bail!(CompileError::UnknownOperator {
                        operator: infix_expr.operator.clone()
                    }),
                };
            }

            ast::Node::IfExpression(if_expr) => {
                // condition
                // jump-not-truthy alternative
                // consequence
                // jump end
                // alternative/OpNull
                // end

                // condition
                self.compile(if_expr.condition.as_ref())
                    .context("failed to compile the condition.")?;

                // jump-not-truthy alternative
                let jump_not_truthy_pos = self
                    .add_inst(OpCodeKind::JumpNotTruthy, &[9999])
                    .context("failed to add the jump-not-truthy instruction.")?;

                // consequence
                self.compile(&if_expr.consequence)
                    .context("failed to compile the consequence block.")?;
                if self.last_inst_is(OpCodeKind::Pop) {
                    self.remove_last_inst();
                }

                // jump end
                let jump_pos = self
                    .add_inst(OpCodeKind::Jump, &[9999])
                    .context("failed to add the jump instruction.")?;

                // overwrite jump-not-truthy
                let alternative_pos = self.bytecode.instructions.len();
                self.change_operands(jump_not_truthy_pos, &[alternative_pos as i64])
                    .context("failed to change operands of the jump-not-truthy instruction.")?;

                // alternative
                if let Some(alternative) = if_expr.alternative.as_ref() {
                    self.compile(alternative)
                        .context("failed to copile the alternative block.")?;
                    if self.last_inst_is(OpCodeKind::Pop) {
                        self.remove_last_inst();
                    }
                } else {
                    self.add_inst(OpCodeKind::Null, &[])
                        .context("failed to push a null instruction.")?;
                }

                // overwrite jump
                let end_pos = self.bytecode.instructions.len();
                self.change_operands(jump_pos, &[end_pos as i64])
                    .context("failed to change operands of the jump instruction.")?;
            }

            ast::Node::BlockStatement(block_stmt) => self.compile_block_statement(block_stmt)?,

            ast::Node::IntegerLiteral(int_literal) => {
                let int_obj = object::Object::int(int_literal.value);

                let idx = self.add_const(Arc::new(int_obj));
                let operands = [idx as i64];

                self.add_inst(OpCodeKind::Constant, &operands)
                    .context("failed to add the constant instuction.")?;
            }

            ast::Node::BoolLiteral(bool_literal) => {
                if bool_literal.value {
                    self.add_inst(OpCodeKind::True, &[])
                        .context("failed to add the bool instruction.")?;
                } else {
                    self.add_inst(OpCodeKind::False, &[])
                        .context("failed to add the bool instruction.")?;
                }
            }

            _ => unimplemented!(),
        }

        Ok(())
    }

    fn compile_block_statement(&mut self, block_stmt: &BlockStatement) -> Result<()> {
        // block statementに文が一つも含まれない場合に何が評価されるのかが本を見てもわからなかったため、nullを評価する文を自動で追加するようにした
        if block_stmt.statements.is_empty() {
            self.add_inst(OpCodeKind::Null, &[])
                .context("failed to add a null instruction.")?;
            self.add_inst(OpCodeKind::Pop, &[])
                .context("failed to add an pop instruction.")?;
            return Ok(());
        }

        for stmt in block_stmt.statements.iter() {
            self.compile(stmt)
                .context("failed to compile a statement")?;
        }

        Ok(())
    }

    pub fn get_bytecode(&self) -> &ByteCode {
        &self.bytecode
    }
}

#[derive(Debug, Clone)]
pub struct AddedInstruction {
    kind: OpCodeKind,
    position: usize,
}

impl AddedInstruction {
    pub const fn new(kind: OpCodeKind, position: usize) -> Self {
        Self { kind, position }
    }
}

mod test {
    use std::sync::Arc;

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
                "wrong instructions length.\nexpected: {} got: {}\nexpected insts: {}\nactual insts: {}",
                expected.len(),
                actual.len(),
                disasm(expected),
                disasm(actual)
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

    fn test_consts(expected: &[Object], actual: &[Arc<Object>]) -> Result<()> {
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
                    test_integer_object(int_obj.read().unwrap().value, &actual[i])
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
                if integer_object.read().unwrap().value != expected {
                    bail!(
                        "object has wrong value. expected: {}, got: {}.",
                        expected,
                        integer_object.read().unwrap().value
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
                "1 - 2",
                &[Object::int(1), Object::int(2)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::Sub, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "1 * 2",
                &[Object::int(1), Object::int(2)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::Mul, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "2 / 1",
                &[Object::int(2), Object::int(1)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::Div, &[]).unwrap(),
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
            CompilerTestCase::new(
                "-1",
                &[Object::int(1)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Minus, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "!true",
                &[],
                &[
                    create_inst(OpCodeKind::True, &[]).unwrap(),
                    create_inst(OpCodeKind::Bang, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
        ];

        run_compiler_tests(&tests);
    }

    #[test]
    fn test_bool_expressions() {
        let tests = [
            CompilerTestCase::new(
                "true",
                &[],
                &[
                    create_inst(OpCodeKind::True, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "false",
                &[],
                &[
                    create_inst(OpCodeKind::False, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "1 > 2",
                &[Object::int(1), Object::int(2)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::GreaterThan, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "1 < 2",
                &[Object::int(2), Object::int(1)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::GreaterThan, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "1 == 2",
                &[Object::int(1), Object::int(2)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::Equal, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "1 != 2",
                &[Object::int(1), Object::int(2)],
                &[
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::NotEqual, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "true == false",
                &[],
                &[
                    create_inst(OpCodeKind::True, &[]).unwrap(),
                    create_inst(OpCodeKind::False, &[]).unwrap(),
                    create_inst(OpCodeKind::Equal, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "true != false",
                &[],
                &[
                    create_inst(OpCodeKind::True, &[]).unwrap(),
                    create_inst(OpCodeKind::False, &[]).unwrap(),
                    create_inst(OpCodeKind::NotEqual, &[]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
        ];

        run_compiler_tests(&tests);
    }

    #[test]
    fn test_conditionals() {
        let tests = [
            CompilerTestCase::new(
                "if (true) { 10 }; 3333;",
                &[Object::int(10), Object::int(3333)],
                &[
                    // 0000
                    create_inst(OpCodeKind::True, &[]).unwrap(),
                    // 0001
                    create_inst(OpCodeKind::JumpNotTruthy, &[10]).unwrap(),
                    // 0004
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    // 0007
                    create_inst(OpCodeKind::Jump, &[11]).unwrap(),
                    // 0010
                    create_inst(OpCodeKind::Null, &[]).unwrap(),
                    // 0011
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                    // 0012
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    // 0015
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
            CompilerTestCase::new(
                "if (true) { 10 } else { 20 }; 3333;",
                &[Object::int(10), Object::int(20), Object::int(3333)],
                &[
                    create_inst(OpCodeKind::True, &[]).unwrap(),
                    create_inst(OpCodeKind::JumpNotTruthy, &[10]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[0]).unwrap(),
                    create_inst(OpCodeKind::Jump, &[13]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[1]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                    create_inst(OpCodeKind::Constant, &[2]).unwrap(),
                    create_inst(OpCodeKind::Pop, &[]).unwrap(),
                ],
            ),
        ];

        run_compiler_tests(&tests);
    }
}
