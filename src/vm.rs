use std::sync::{self, LazyLock, PoisonError};
use std::sync::{Arc, RwLock};

use anyhow::{Context, Result, anyhow, bail};
use thiserror::Error;

use crate::code::OpCodeKind;
use crate::compiler::ByteCode;
use crate::object::{BoolObject, IntegerObject, Object};
use crate::utils::u16_from_be_bytes;

const STACK_SIZE: usize = 2048;

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("instruction pointer overflow. length: {inst_length}, ip: {inst_pointer}")]
    InstructionPointerOverflow {
        inst_length: usize,
        inst_pointer: usize,
    },

    #[error("unknown opcode byte: {byte}")]
    UnknownOpCodeByte { byte: u8 },

    #[error("stack overflow")]
    StackOverflow,

    #[error(
        "constants overflow. length of the global constants array is `{size}`, and constant associated with `{idx}` is not found."
    )]
    ConstantsOverflow { size: usize, idx: usize },

    #[error("cannot pop from the stack because it is empty.")]
    PopFromEmptyStack,

    #[error("unknown types of operands for infix operation. left: {left}, right: {right}.")]
    UnknownOperandsTypesForInfixOperation { left: String, right: String },

    #[error("unknown type of operand for prefix operation. left: {left}, operator: {operator}.")]
    UnknownOperandTypeForPrefixOperation { left: String, operator: String },

    #[error("`{left}` and `{right}` pair is not supported for infix operation `{operation:?}`.")]
    UnsupportedInfixOperation {
        left: String,
        right: String,
        operation: OpCodeKind,
    },

    #[error("race error: {msg}")]
    RaceError { msg: String },
}

static TRUE: LazyLock<Arc<Object>> = LazyLock::new(|| Arc::new(Object::bool(true)));
static FALSE: LazyLock<Arc<Object>> = LazyLock::new(|| Arc::new(Object::bool(false)));
static NULL: LazyLock<Arc<Object>> = LazyLock::new(|| Arc::new(Object::null()));

pub struct Vm {
    constants: Vec<Arc<Object>>,
    instructions: Vec<u8>,
    stack: Vec<Arc<Object>>,
    sp: usize,
    last_stack_top: Option<Arc<Object>>,
}

impl Vm {
    pub fn new(bytecode: &ByteCode) -> Self {
        let mut stack = Vec::with_capacity(STACK_SIZE);

        stack.resize(STACK_SIZE, Arc::new(Object::null()));

        Self {
            constants: bytecode.constants.clone(),
            instructions: bytecode.instructions.clone(),
            stack,
            sp: 0,
            last_stack_top: None,
        }
    }

    fn read_n(&self, pos: usize, n: usize) -> Result<&[u8]> {
        if let Some(x) = self.instructions.get(pos..pos + 2) {
            Ok(x)
        } else {
            bail!(RuntimeError::InstructionPointerOverflow {
                inst_length: self.instructions.len(),
                inst_pointer: pos + 2
            });
        }
    }

    pub fn run(&mut self) -> Result<()> {
        let mut ip = 0;

        while ip < self.instructions.len() {
            // 命令の取得
            let op_kind = match self.instructions.get(ip) {
                Some(x) => match OpCodeKind::from_u8(*x) {
                    Ok(y) => y,
                    Err(_) => {
                        bail!(RuntimeError::UnknownOpCodeByte { byte: *x });
                    }
                },
                None => {
                    bail!(RuntimeError::InstructionPointerOverflow {
                        inst_length: self.instructions.len(),
                        inst_pointer: ip,
                    });
                }
            };
            ip += 1;

            // 命令ごとの処理
            match op_kind {
                OpCodeKind::Constant => {
                    // 定数配列のインデックスを取得する
                    let raw_operands = self.read_n(ip, 2)?;

                    //// 上の処理で幅が2であることは確定済みなのでunwrapしても良い
                    let const_idx = u16_from_be_bytes(raw_operands).unwrap() as usize;
                    ip += 2;

                    // 定数を取得する
                    let const_value = match self.constants.get(const_idx) {
                        Some(x) => x,
                        None => bail!(RuntimeError::ConstantsOverflow {
                            size: self.constants.len(),
                            idx: const_idx
                        }),
                    };

                    // 定数をスタックにpushする
                    self.push(const_value.clone())
                        .context("failed to push the constant.")?;
                }

                // infix expressions
                OpCodeKind::Add | OpCodeKind::Sub | OpCodeKind::Mul | OpCodeKind::Div => {
                    self.execute_binary_operation(op_kind)
                        .context("failed to execute infix operation.")?;
                }

                OpCodeKind::Equal | OpCodeKind::NotEqual | OpCodeKind::GreaterThan => {
                    self.execute_comparison(op_kind)
                        .context("failed to execute comparison")?;
                }

                // bool
                OpCodeKind::True => {
                    self.push(TRUE.clone()).context("failed to push `true`.")?;
                }

                OpCodeKind::False => {
                    self.push(FALSE.clone())
                        .context("failed to push `false`.")?;
                }

                // null
                OpCodeKind::Null => {
                    self.push(NULL.clone()).context("failed to push `null`.")?;
                }

                // pop
                OpCodeKind::Pop => {
                    self.pop().context("failed to pop from the stack.")?;
                }

                // prefix expressions
                OpCodeKind::Bang => {
                    let left = self.pop().context("failed to pop the left value.")?;

                    match left.as_ref() {
                        Object::Bool(bool_obj) => {
                            let left = bool_obj
                                .read()
                                .map_err(|err| RuntimeError::RaceError {
                                    msg: err.to_string(),
                                })
                                .context("failed to read the left value.")?;

                            let result = !left.value;

                            self.push(Arc::new(Object::bool(result)))
                                .context("failed to push the result.")?;
                        }
                        Object::Null(_) => {
                            self.push(Arc::new(Object::bool(true)))
                                .context("failed to push the result.")?;
                        }
                        _ => {
                            self.push(Arc::new(Object::bool(false)))
                                .context("failed to push the result.")?;
                        }
                    }
                }

                OpCodeKind::Minus => {
                    let left = self.pop().context("failed to pop the left value.")?;

                    if let Object::Integer(int_obj) = left.as_ref() {
                        let left = int_obj
                            .read()
                            .map_err(|err| RuntimeError::RaceError {
                                msg: err.to_string(),
                            })
                            .context("failed to read the left value.")?;

                        let result = -left.value;

                        self.push(Arc::new(Object::int(result)))
                            .context("failed to push the result.")?;
                    } else {
                        bail!(RuntimeError::UnknownOperandTypeForPrefixOperation {
                            left: left.to_string(),
                            operator: "-".to_string()
                        });
                    }
                }

                OpCodeKind::Jump => {
                    let raw_operands = self.read_n(ip, 2)?;

                    let pos = u16_from_be_bytes(raw_operands).unwrap() as usize;
                    ip = pos;
                }

                OpCodeKind::JumpNotTruthy => {
                    let raw_operands = self.read_n(ip, 2)?;

                    let pos = u16_from_be_bytes(raw_operands).unwrap() as usize;

                    let condition = self.pop().context("failed to pop the condition.")?;
                    if !condition.is_truthy() {
                        ip = pos;
                    } else {
                        // posを読んだ分
                        ip += 2;
                    }
                }

                _ => unimplemented!(),
            }
        }

        Ok(())
    }

    // 四則演算の実行
    fn execute_binary_operation(&mut self, op_kind: OpCodeKind) -> Result<()> {
        // left -> rightの順番でpushされるのでright -> leftの順番でpopする
        let right = self.pop().context("failed to pop the right value.")?;
        let left = self.pop().context("failed to pop the left value.")?;

        match (left.as_ref(), right.as_ref()) {
            (Object::Integer(left), Object::Integer(right)) => {
                self.execute_integer_binary_operation(op_kind, left.clone(), right.clone())
                    .context("failed to execute integer infix operation.")?;
            }
            _ => bail!(RuntimeError::UnknownOperandsTypesForInfixOperation {
                left: left.to_string(),
                right: right.to_string()
            }),
        }

        Ok(())
    }

    fn execute_integer_binary_operation(
        &mut self,
        op_kind: OpCodeKind,
        left: Arc<RwLock<IntegerObject>>,
        right: Arc<RwLock<IntegerObject>>,
    ) -> Result<()> {
        let result = match op_kind {
            OpCodeKind::Add => left.read().unwrap().value + right.read().unwrap().value,
            OpCodeKind::Sub => left.read().unwrap().value - right.read().unwrap().value,
            OpCodeKind::Mul => left.read().unwrap().value * right.read().unwrap().value,
            OpCodeKind::Div => left.read().unwrap().value / right.read().unwrap().value,
            _ => unreachable!(),
        };

        self.push(Arc::new(Object::int(result)))
            .context("failed to push the result value.")?;

        Ok(())
    }

    // 比較演算の実行
    fn execute_comparison(&mut self, op_kind: OpCodeKind) -> Result<()> {
        // left -> rightの順番でpushされるのでright -> leftの順番でpopする
        let right = self.pop().context("failed to pop the right value.")?;
        let left = self.pop().context("failed to pop the left value.")?;

        match (left.as_ref(), right.as_ref()) {
            (Object::Integer(left), Object::Integer(right)) => {
                self.execute_integer_comparison(op_kind, left.clone(), right.clone())
                    .context("failed to execute integer comparison.")?;
            }
            (Object::Bool(left), Object::Bool(right)) => {
                self.execute_bool_comparison(op_kind, left.clone(), right.clone())
                    .context("failed to execute bool comparison.")?;
            }
            _ => {
                bail!(RuntimeError::UnknownOperandsTypesForInfixOperation {
                    left: left.to_string(),
                    right: right.to_string()
                })
            }
        }

        Ok(())
    }

    fn execute_integer_comparison(
        &mut self,
        op_kind: OpCodeKind,
        left: Arc<RwLock<IntegerObject>>,
        right: Arc<RwLock<IntegerObject>>,
    ) -> Result<()> {
        let left = left
            .read()
            .map_err(|err| RuntimeError::RaceError {
                msg: err.to_string(),
            })?
            .value;
        let right = right
            .read()
            .map_err(|err| RuntimeError::RaceError {
                msg: err.to_string(),
            })?
            .value;

        let result = match op_kind {
            OpCodeKind::Equal => left == right,
            OpCodeKind::NotEqual => left != right,
            OpCodeKind::GreaterThan => left > right,
            _ => unreachable!(),
        };

        self.push(Arc::new(Object::bool(result)))
            .context("failed to push the result value")?;

        Ok(())
    }

    fn execute_bool_comparison(
        &mut self,
        op_kind: OpCodeKind,
        left: Arc<RwLock<BoolObject>>,
        right: Arc<RwLock<BoolObject>>,
    ) -> Result<()> {
        let left = left
            .read()
            .map_err(|err| RuntimeError::RaceError {
                msg: err.to_string(),
            })?
            .value;
        let right = right
            .read()
            .map_err(|err| RuntimeError::RaceError {
                msg: err.to_string(),
            })?
            .value;

        let result = match op_kind {
            OpCodeKind::Equal => left == right,
            OpCodeKind::NotEqual => left != right,
            _ => bail!(RuntimeError::UnsupportedInfixOperation {
                left: format!("{}", left),
                right: format!("{}", right),
                operation: op_kind
            }),
        };

        self.push(Arc::new(Object::bool(result)))
            .context("failed to push the result value")?;

        Ok(())
    }

    fn push(&mut self, obj: Arc<Object>) -> Result<()> {
        if self.sp >= STACK_SIZE {
            bail!(RuntimeError::StackOverflow);
        }

        self.stack[self.sp] = obj;

        self.sp += 1;

        Ok(())
    }

    fn pop(&mut self) -> Result<Arc<Object>> {
        if self.sp == 0 {
            bail!(RuntimeError::PopFromEmptyStack);
        }

        self.sp -= 1;

        let value = self.stack[self.sp].clone();
        self.last_stack_top.replace(value.clone());

        Ok(value)
    }

    pub fn stack_top(&self) -> Option<Arc<Object>> {
        if self.sp == 0 {
            return None;
        }

        Some(self.stack[self.sp - 1].clone())
    }

    pub fn last_stack_top(&self) -> Option<Arc<Object>> {
        self.last_stack_top.clone()
    }
}

mod test {
    use std::sync::Arc;

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

    fn test_integer_object(expected: i64, obj: Arc<object::Object>) -> Result<()> {
        match &*obj {
            object::Object::Integer(inner) => {
                let inner_value = inner.read().unwrap().value;
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
        for (i, test) in tests.iter().enumerate() {
            let program = parse(test.input)
                .with_context(|| format!("test {} failed. failed to parse an input.", i))?;

            let mut compiler = Compiler::new();

            compiler
                .compile(&program)
                .with_context(|| format!("test {} failed. failed to compile a program.", i))?;

            let bytecode = compiler.get_bytecode();
            let mut vm = Vm::new(bytecode);
            vm.run()
                .with_context(|| format!("test {} failed. failed to run a bytecode.", i))?;

            let last_stack_top = vm.last_stack_top();
            test_expected_object(&test.expected, last_stack_top)?;
        }
        Ok(())
    }

    fn test_expected_object(
        expected: &object::Object,
        obj: Option<Arc<object::Object>>,
    ) -> Result<()> {
        let obj = if let Some(o) = obj {
            o
        } else {
            bail!("obj is None.");
        };

        match (expected, obj.as_ref()) {
            (object::Object::Integer(expected), object::Object::Integer(actual)) => {
                let expected = expected.read().unwrap().value;
                let actual = actual.read().unwrap().value;
                if expected != actual {
                    bail!(
                        "object has wrong value. expected: {}, got: {}.",
                        expected,
                        actual
                    )
                }
            }

            (object::Object::Bool(expected), object::Object::Bool(actual)) => {
                let expected = expected.read().unwrap().value;
                let actual = actual.read().unwrap().value;
                if expected != actual {
                    bail!(
                        "object has wrong value. expected: {}, got: {}.",
                        expected,
                        actual
                    )
                }
            }

            (object::Object::Null(_), object::Object::Null(_)) => {}

            _ => {
                return Err(anyhow::anyhow!(
                    "unsupported objects: {} and {}",
                    expected,
                    obj
                ));
            }
        }
        Ok(())
    }

    #[test]
    fn test_integer_arithmetic() {
        let tests = [
            VmTestCase::new("1", object::Object::int(1)),
            VmTestCase::new("2", object::Object::int(2)),
            VmTestCase::new("1 + 2", object::Object::int(3)),
            VmTestCase::new("1 - 2", object::Object::int(-1)),
            VmTestCase::new("1 * 2", object::Object::int(2)),
            VmTestCase::new("4 / 2", object::Object::int(2)),
            VmTestCase::new("50 / 2 * 2 + 10 - 5", object::Object::int(55)),
            VmTestCase::new("5 + 5 + 5 + 5 - 10", object::Object::int(10)),
            VmTestCase::new("2 * 2 * 2 * 2 * 2", object::Object::int(32)),
            VmTestCase::new("5 * 2 + 10", object::Object::int(20)),
            VmTestCase::new("5 + 2 * 10", object::Object::int(25)),
            VmTestCase::new("5 * (2 + 10)", object::Object::int(60)),
            VmTestCase::new("-5", object::Object::int(-5)),
            VmTestCase::new("-10", object::Object::int(-10)),
            VmTestCase::new("-50 + 100 + -50", object::Object::int(0)),
            VmTestCase::new("(5 + 10 * 2 + 15 / 3) * 2 + -10", object::Object::int(50)),
        ];
        run_vm_tests(&tests).expect("a vm test failed.");
    }

    #[test]
    fn test_bool_expressions() {
        let tests = [
            VmTestCase::new("true", object::Object::bool(true)),
            VmTestCase::new("false", object::Object::bool(false)),
            VmTestCase::new("1 < 2", object::Object::bool(true)),
            VmTestCase::new("1 > 2", object::Object::bool(false)),
            VmTestCase::new("1 < 1", object::Object::bool(false)),
            VmTestCase::new("1 > 1", object::Object::bool(false)),
            VmTestCase::new("1 == 1", object::Object::bool(true)),
            VmTestCase::new("1 != 1", object::Object::bool(false)),
            VmTestCase::new("1 == 2", object::Object::bool(false)),
            VmTestCase::new("1 != 2", object::Object::bool(true)),
            VmTestCase::new("true == true", object::Object::bool(true)),
            VmTestCase::new("false == false", object::Object::bool(true)),
            VmTestCase::new("true == false", object::Object::bool(false)),
            VmTestCase::new("true != false", object::Object::bool(true)),
            VmTestCase::new("false != true", object::Object::bool(true)),
            VmTestCase::new("(1 < 2) == true", object::Object::bool(true)),
            VmTestCase::new("(1 < 2) == false", object::Object::bool(false)),
            VmTestCase::new("(1 > 2) == true", object::Object::bool(false)),
            VmTestCase::new("(1 > 2) == false", object::Object::bool(true)),
            VmTestCase::new("!true", object::Object::bool(false)),
            VmTestCase::new("!false", object::Object::bool(true)),
            VmTestCase::new("!5", object::Object::bool(false)),
            VmTestCase::new("!!true", object::Object::bool(true)),
            VmTestCase::new("!!false", object::Object::bool(false)),
            VmTestCase::new("!!5", object::Object::bool(true)),
            VmTestCase::new("!(if (false) { 5; })", object::Object::bool(true)),
        ];

        run_vm_tests(&tests).expect("a vm test failed.");
    }

    #[test]
    fn test_conditionals() {
        let tests = [
            VmTestCase::new("if (true) { 10 }", object::Object::int(10)),
            VmTestCase::new("if (true) { 10 } else { 20 }", object::Object::int(10)),
            VmTestCase::new("if (false) { 10 } else { 20 }", object::Object::int(20)),
            VmTestCase::new("if (1) { 10 }", object::Object::int(10)),
            VmTestCase::new("if (1 < 2) { 10 }", object::Object::int(10)),
            VmTestCase::new("if (1 < 2) { 10 } else { 20 }", object::Object::int(10)),
            VmTestCase::new("if (1 > 2) { 10 } else { 20 }", object::Object::int(20)),
            VmTestCase::new("if (1 > 2) { 10 }", object::Object::null()),
            VmTestCase::new("if (false) { 10 }", object::Object::null()),
            VmTestCase::new(
                "if ((if (false) { 10 })) { 10 } else { 20 }",
                object::Object::int(20),
            ),
            VmTestCase::new("if (false) {}", object::Object::null()),
            VmTestCase::new("if (false) {} else {}", object::Object::null()),
            VmTestCase::new("if (true) {} else {}", object::Object::null()),
        ];

        run_vm_tests(&tests).expect("a vm test failed.");
    }
}
