use std::rc::Rc;

use anyhow::{Context, Result, bail};
use thiserror::Error;

use crate::code::{Instruction, Instructions, OpCodeKind};
use crate::compiler::ByteCode;
use crate::object::Object;
use crate::utils::u16_from_be_bytes;

const STACK_SIZE: usize = 2048;

#[derive(Debug, Error)]
pub enum VmError {
    #[error("instruction pointer overflow. length: {instruction_length}, ip: {instruction_length}")]
    InstructionPointerOverflow {
        instruction_length: usize,
        instruction_pointer: usize,
    },

    #[error("unknown opcode byte: {byte}")]
    UnknownOpCodeByte { byte: u8 },

    #[error("stack overflow")]
    StackOverflow,

    #[error(
        "constants overflow. length of the global constants array is `{size}`, and constant associated with `{idx}` is not found."
    )]
    ConstantsOverflow { size: usize, idx: usize },
}

pub struct Vm {
    constants: Vec<Rc<Object>>,
    instructions: Instructions,
    stack: Vec<Rc<Object>>,
    sp: usize,
}

impl Vm {
    pub fn new(bytecode: &ByteCode) -> Self {
        let mut stack = Vec::with_capacity(STACK_SIZE);

        stack.resize(STACK_SIZE, Rc::new(Object::null()));

        Self {
            constants: bytecode.constants.clone(),
            instructions: bytecode.instructions.clone(),
            stack,
            sp: 0,
        }
    }

    pub fn run(&mut self) -> Result<()> {
        let mut ip = 0;

        while ip < self.instructions.len() {
            // 命令の取得
            //// ここでlookup関数などを実行するとクソ遅くなるので生のバイトから変換したほうが良い (今の実装はそう)
            let op_kind = if let Some(b) = self.instructions.get(ip) {
                if let Ok(o) = OpCodeKind::from_u8(*b) {
                    o
                } else {
                    bail!(VmError::UnknownOpCodeByte { byte: *b });
                }
            } else {
                bail!(VmError::InstructionPointerOverflow {
                    instruction_length: self.instructions.len(),
                    instruction_pointer: ip,
                });
            };
            ip += 1;

            // 命令ごとの処理
            match op_kind {
                OpCodeKind::Constant => {
                    // 定数配列へのインデックスを取得する
                    let raw_operands = if let Some(x) = self.instructions.get(ip..ip + 2) {
                        x
                    } else {
                        bail!(VmError::InstructionPointerOverflow {
                            instruction_length: self.instructions.len(),
                            instruction_pointer: ip + 2
                        });
                    };

                    //// 上の処理で幅が2であることは確定済みなのでunwrapしても良い
                    let const_idx = u16_from_be_bytes(raw_operands).unwrap() as usize;
                    ip += 2;

                    // 定数を取得する
                    let const_value = match self.constants.get(const_idx) {
                        Some(x) => x,
                        None => bail!(VmError::ConstantsOverflow {
                            size: self.constants.len(),
                            idx: const_idx
                        }),
                    };

                    // 定数をスタックにpushする
                    self.push(const_value.clone());

                    println!("const_idx: {}", const_idx);
                }
            }
        }

        // todo!()
        Ok(())
    }

    fn push(&mut self, obj: Rc<Object>) -> Result<()> {
        if self.sp >= STACK_SIZE {
            bail!(VmError::StackOverflow);
        }

        self.stack[self.sp] = obj;

        self.sp += 1;

        Ok(())
    }

    pub fn stack_top(&self) -> Option<Rc<Object>> {
        if self.sp == 0 {
            return None;
        }

        Some(self.stack[self.sp - 1].clone())
    }
}

mod test {
    use std::rc::Rc;

    use anyhow::{Context, Result, bail};

    use crate::compiler::Compiler;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::{ast, object};

    use super::Vm;

    fn parse(input: &str) -> Result<ast::Program> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program()?;
        Ok(program)
    }

    fn test_integer_object(expected: i64, obj: Rc<object::Object>) -> Result<()> {
        match &*obj {
            object::Object::Integer(inner) => {
                let inner_value = inner.borrow().value;
                if inner_value != expected {
                    bail!(
                        "object has wrong value. expected: {}, got: {}.",
                        expected,
                        inner_value
                    )
                }
            }
            _ => {
                return Err(anyhow::anyhow!("object is not Integer. got={}", obj));
            }
        }
        Ok(())
    }

    struct VmTestCase {
        input: &'static str,
        expected: object::Object,
    }

    impl VmTestCase {
        fn new(input: &'static str, expected: object::Object) -> Self {
            Self { input, expected }
        }
    }

    fn run_vm_tests(tests: &[VmTestCase]) -> Result<()> {
        for test in tests.iter() {
            let program = parse(test.input).context("failed to parse an input.")?;

            let mut compiler = Compiler::new();

            compiler
                .compile(&program)
                .context("failed to compile a program.")?;

            let bytecode = compiler.get_bytecode();
            let mut vm = Vm::new(bytecode);
            vm.run().context("failed to run a bytecode.")?;

            let stack_top = vm.stack_top();
            test_expected_object(&test.expected, stack_top)?;
        }
        Ok(())
    }

    fn test_expected_object(
        expected: &object::Object,
        obj: Option<Rc<object::Object>>,
    ) -> Result<()> {
        let obj = if let Some(o) = obj {
            o
        } else {
            bail!("obj is None.");
        };

        match (expected, obj.as_ref()) {
            (object::Object::Integer(expected), object::Object::Integer(actual)) => {
                let expected = expected.borrow().value;
                let actual = actual.borrow().value;
                if expected != actual {
                    bail!(
                        "object has wrong value. expected: {}, got: {}.",
                        expected,
                        actual
                    )
                }
            }
            _ => {
                return Err(anyhow::anyhow!("object is not Integer. got: {}", obj));
            }
        }
        Ok(())
    }

    #[test]
    fn test_integer_arithmetic() -> Result<()> {
        let tests = [
            VmTestCase::new("1", object::Object::int(1)),
            VmTestCase::new("2", object::Object::int(2)),
            VmTestCase::new("1 + 2", object::Object::int(3)),
        ];
        run_vm_tests(&tests)
    }
}
