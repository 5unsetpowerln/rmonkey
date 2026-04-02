use std::collections::HashMap;
use std::fmt;
use std::ops::Deref;
use std::sync::LazyLock;

use anyhow::{Context, Result, bail, ensure};
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[repr(u8)]
pub enum OpCodeKind {
    Constant,
    Add,
    Pop,
}

impl OpCodeKind {
    pub fn from_u8(byte: u8) -> Result<Self> {
        match byte {
            b if b == Self::Constant as u8 => Ok(Self::Constant),
            b if b == Self::Add as u8 => Ok(Self::Add),
            b if b == Self::Pop as u8 => Ok(Self::Pop),
            _ => bail!(CodeError::UnknownOpCodeByte { byte }),
        }
    }
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
            OpCodeKind::Add => &Self::ADD,
            OpCodeKind::Pop => &Self::POP,
        }
    }

    pub fn lookup_byte(byte: u8) -> Result<&'static Self> {
        let kind = OpCodeKind::from_u8(byte)?;
        Ok(Self::lookup(kind))
    }

    const CONSTANT: OpCodeDef = OpCodeDef::new(OpCodeKind::Constant, "OpConstant", &[2]);
    const ADD: OpCodeDef = OpCodeDef::new(OpCodeKind::Add, "OpAdd", &[]);
    const POP: OpCodeDef = OpCodeDef::new(OpCodeKind::Pop, "OpPop", &[]);
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

    //     #[test]
    //     fn test_instruction_to_bytes_method() {
    //         let inst = Instruction::new(OpCodeKind::Constant, &[0xfffe]).unwrap();
    //         let bytes = inst.to_bytes();
    //         assert_eq!(bytes, vec![OpCodeKind::Constant as u8, 0xff, 0xfe]);
    //     }

    //     #[test]
    //     fn test_instructions_add_method() {
    //         let mut insts = Instructions::new();
    //         let pos0 = insts.add_inst(&Instruction::new(OpCodeKind::Constant, &[1]).unwrap());
    //         let pos1 = insts.add_inst(&Instruction::new(OpCodeKind::Constant, &[2]).unwrap());

    //         assert_eq!(pos0, 0);
    //         assert_eq!(pos1, 3);
    //         assert_eq!(insts.len(), 6);
    //     }

    //     #[test]
    //     fn test_read_from() {
    //         let inst = Instruction::new(OpCodeKind::Constant, &[65535]).unwrap();
    //         let bytes = inst.to_bytes();

    //         let (decoded, bytes_read) = Instruction::read_from(&bytes, 0).unwrap();

    //         assert_eq!(bytes_read, 3);
    //         assert_eq!(decoded.opcode.opcode_kind, OpCodeKind::Constant);
    //         assert_eq!(decoded.operands, vec![65535]);
    //     }

    //     #[test]
    //     fn test_wrong_operand_count() {
    //         assert!(Instruction::new(OpCodeKind::Constant, &[]).is_err());
    //         assert!(Instruction::new(OpCodeKind::Constant, &[1, 2]).is_err());
    //     }
}
