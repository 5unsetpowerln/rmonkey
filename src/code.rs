use std::collections::HashMap;
use std::fmt;
use std::ops::Deref;
use std::sync::LazyLock;

use anyhow::{Context, Result, bail, ensure};
use derive_from_u8::FromU8;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CodeError {
    #[error("definition for opcode `{opcode:?}` not found.")]
    DefinitionNotFound { opcode: OpCodeDef },
    #[error("wrong number of operands for `{kind:?}`. expected: {expected}, got: {got}")]
    WrongNumberOfOperands {
        kind: OpCodeKind,
        expected: usize,
        got: usize,
    },
    #[error("unknown opcode byte: {byte}")]
    UnknownOpCodeByte { byte: u8 },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, FromU8)]
#[repr(u8)]
pub enum OpCodeKind {
    Constant,
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    True,
    False,
    Equal,
    NotEqual,
    GreaterThan,
    Minus,
    Bang,
}

#[derive(Debug)]
pub struct OpCodeDef {
    pub opcode_kind: OpCodeKind,
    pub name: &'static str,
    pub operand_widths: &'static [usize],
}

impl OpCodeDef {
    pub const fn new(
        opcode_kind: OpCodeKind,
        name: &'static str,
        operand_widths: &'static [usize],
    ) -> Self {
        Self {
            opcode_kind,
            name,
            operand_widths,
        }
    }

    pub fn lookup(kind: OpCodeKind) -> &'static Self {
        match kind {
            OpCodeKind::Constant => &Self::CONSTANT,
            OpCodeKind::Pop => &Self::POP,
            OpCodeKind::Add => &Self::ADD,
            OpCodeKind::Sub => &Self::SUB,
            OpCodeKind::Mul => &Self::MUL,
            OpCodeKind::Div => &Self::DIV,
            OpCodeKind::True => &Self::TRUE,
            OpCodeKind::False => &Self::FALSE,
            OpCodeKind::Equal => &Self::EQUAL,
            OpCodeKind::NotEqual => &Self::NOT_EQUAL,
            OpCodeKind::GreaterThan => &Self::GREATER_THAN,
            OpCodeKind::Minus => &Self::MINUS,
            OpCodeKind::Bang => &Self::BANG,
        }
    }

    pub fn lookup_byte(byte: u8) -> Result<&'static Self> {
        let kind = OpCodeKind::from_u8(byte)?;
        Ok(Self::lookup(kind))
    }

    const CONSTANT: OpCodeDef = OpCodeDef::new(OpCodeKind::Constant, "OpConstant", &[2]);
    const POP: OpCodeDef = OpCodeDef::new(OpCodeKind::Pop, "OpPop", &[]);

    const ADD: OpCodeDef = OpCodeDef::new(OpCodeKind::Add, "OpAdd", &[]);
    const SUB: OpCodeDef = OpCodeDef::new(OpCodeKind::Add, "OpSub", &[]);
    const MUL: OpCodeDef = OpCodeDef::new(OpCodeKind::Add, "OpMul", &[]);
    const DIV: OpCodeDef = OpCodeDef::new(OpCodeKind::Add, "OpDiv", &[]);

    const TRUE: OpCodeDef = OpCodeDef::new(OpCodeKind::Add, "OpTrue", &[]);
    const FALSE: OpCodeDef = OpCodeDef::new(OpCodeKind::Add, "OpFalse", &[]);

    const EQUAL: OpCodeDef = OpCodeDef::new(OpCodeKind::Equal, "OpEqual", &[]);
    const NOT_EQUAL: OpCodeDef = OpCodeDef::new(OpCodeKind::NotEqual, "OpNotEqual", &[]);
    const GREATER_THAN: OpCodeDef = OpCodeDef::new(OpCodeKind::GreaterThan, "OpGreaterThan", &[]);

    const MINUS: OpCodeDef = OpCodeDef::new(OpCodeKind::Minus, "OpMinus", &[]);
    const BANG: OpCodeDef = OpCodeDef::new(OpCodeKind::Bang, "OpBang", &[]);
}

impl fmt::Display for OpCodeDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

pub fn create_inst(kind: OpCodeKind, operands: &[i64]) -> Result<Vec<u8>> {
    let def = OpCodeDef::lookup(kind);

    // 本では渡されたオペランドの数が定義されているオペランドの幅リストの長さよりも小さかった場合についての処理が明示されていない
    // ここではとりあえず違っていたらエラーを投げるようにする
    ensure!(
        def.operand_widths.len() == operands.len(),
        CodeError::WrongNumberOfOperands {
            kind,
            expected: def.operand_widths.len(),
            got: operands.len()
        }
    );

    let mut inst_len = 1;
    for w in def.operand_widths.iter() {
        inst_len += w;
    }

    let mut inst = Vec::new();
    inst.push(kind as u8);

    for (i, o) in operands.iter().enumerate() {
        let w = def.operand_widths[i];
        match w {
            2 => {
                inst.extend_from_slice(&(*o as u16).to_be_bytes());
            }
            _ => {
                unimplemented!();
            }
        }
    }

    assert!(inst_len == inst.len());

    Ok(inst)
}

pub fn insts_from_inst_list(list: &[Vec<u8>]) -> Vec<u8> {
    let total: usize = list.iter().map(|v| v.len()).sum();
    let mut insts = Vec::with_capacity(total);
    list.iter().for_each(|inst| {
        insts.extend_from_slice(inst);
    });
    insts
}

mod test {
    use crate::code::{OpCodeKind, create_inst};
    use crate::utils::print_errors;

    #[test]
    fn test_create_inst() {
        struct TestCase {
            kind: OpCodeKind,
            operands: Vec<i64>,
            expected: Vec<u8>,
        }
        impl TestCase {
            fn new(kind: OpCodeKind, operands: &[i64], expected: &[u8]) -> Self {
                Self {
                    kind,
                    operands: operands.to_vec(),
                    expected: expected.to_vec(),
                }
            }
        }

        let tests = [
            TestCase::new(
                OpCodeKind::Constant,
                &[0xfffe],
                &[OpCodeKind::Constant as u8, 0xff, 0xfe],
            ),
            TestCase::new(OpCodeKind::Add, &[], &[OpCodeKind::Add as u8]),
        ];

        for (i, test) in tests.iter().enumerate() {
            let inst = create_inst(test.kind, &test.operands).unwrap_or_else(|err| {
                print_errors("failed to create an instruction", err);
                panic!("test {} failed", i);
            });

            if inst.len() != test.expected.len() {
                panic!(
                    "test {} failed. instruction has wrong length. expected: {}, got: {}",
                    i,
                    test.expected.len(),
                    inst.len()
                );
            }

            for (j, b) in test.expected.iter().enumerate() {
                if inst[j] != *b {
                    panic!(
                        "test {} failed. wrong byte at {}. expected: {}, got: {}",
                        i, j, b, inst[j]
                    );
                }
            }
        }
    }
}
