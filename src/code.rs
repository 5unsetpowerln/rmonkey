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
}

impl OpCodeKind {
    pub fn from_u8(byte: u8) -> Result<Self> {
        match byte {
            b if b == Self::Constant as u8 => Ok(Self::Constant),
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
        }
    }

    pub fn lookup_byte(byte: u8) -> Result<&'static Self> {
        let kind = OpCodeKind::from_u8(byte)?;
        Ok(&Self::lookup(kind))
    }

    const CONSTANT: OpCodeDef = OpCodeDef::new(OpCodeKind::Constant, "OpConstant", &[2]);
    const ADD: OpCodeDef = OpCodeDef::new(OpCodeKind::Add, "OpAdd", &[]);
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

// // Instruction
// #[derive(Debug, Clone)]
// pub struct Instruction {
//     pub opcode: &'static OpCodeDef,
//     pub operands: Vec<u64>,
// }

// impl Instruction {
//     pub fn new(kind: OpCodeKind, operands: &[u64]) -> Result<Self> {
//         let opcode = OpCodeDef::lookup(kind);

//         if operands.len() != opcode.operand_widths.len() {
//             bail!(CodeError::WrongNumberOfOperands {
//                 kind,
//                 expected: opcode.operand_widths.len(),
//                 got: operands.len()
//             });
//         }

//         Ok(Self {
//             opcode,
//             operands: operands.to_vec(),
//         })
//     }

//     pub fn to_bytes(&self) -> Vec<u8> {
//         let total_len: usize = 1 + self.opcode.operand_widths.iter().sum::<usize>();
//         let mut buf = Vec::with_capacity(total_len);

//         buf.push(self.opcode.opcode_kind as u8);

//         for (i, &operand) in self.operands.iter().enumerate() {
//             match self.opcode.operand_widths[i] {
//                 1 => buf.push(operand as u8),
//                 2 => buf.extend_from_slice(&(operand as u16).to_be_bytes()),
//                 4 => buf.extend_from_slice(&(operand as u32).to_be_bytes()),
//                 8 => buf.extend_from_slice(&operand.to_be_bytes()),
//                 w => unimplemented!("operand width {} not supported", w),
//             }
//         }

//         buf
//     }

//     pub fn read_from(bytes: &[u8], offset: usize) -> Result<(Self, usize)> {
//         let opcode = OpCodeDef::lookup_byte(bytes[offset])?;
//         let mut operands = Vec::with_capacity(opcode.operand_widths.len());
//         let mut pos = offset + 1;

//         for &width in opcode.operand_widths {
//             let operand = match width {
//                 1 => bytes[pos] as u64,
//                 2 => u16::from_be_bytes(bytes[pos..pos + 2].try_into().unwrap()) as u64,
//                 4 => u32::from_be_bytes(bytes[pos..pos + 4].try_into().unwrap()) as u64,
//                 8 => u64::from_be_bytes(bytes[pos..pos + 8].try_into().unwrap()),
//                 w => unimplemented!("operand width {} not supported", w),
//             };
//             operands.push(operand);
//             pos += width;
//         }

//         let bytes_read = pos - offset;
//         Ok((Self { opcode, operands }, bytes_read))
//     }
// }

// impl fmt::Display for Instruction {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "{}", self.opcode.name)?;
//         for operand in &self.operands {
//             write!(f, " {}", operand)?;
//         }
//         Ok(())
//     }
// }

// // Instructions
// #[derive(Debug, Clone, PartialEq, Default)]
// pub struct Instructions(pub Vec<u8>);

// impl Instructions {
//     pub fn new() -> Self {
//         Self(Vec::new())
//     }

//     pub fn add_inst(&mut self, inst: &Instruction) -> usize {
//         let pos = self.0.len();
//         self.0.extend_from_slice(&inst.to_bytes());
//         pos
//     }

//     pub fn from_inst_list(list: &[Instructions]) -> Self {
//         let total: usize = list.iter().map(|i| i.0.len()).sum();
//         let mut buf = Vec::with_capacity(total);
//         for insts in list {
//             buf.extend_from_slice(&insts.0);
//         }
//         Self(buf)
//     }
// }

// impl fmt::Display for Instructions {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         let mut offset = 0;
//         while offset < self.0.len() {
//             match Instruction::read_from(&self.0, offset) {
//                 Ok((inst, bytes_read)) => {
//                     writeln!(f, "{:04} {}", offset, inst)?;
//                     offset += bytes_read;
//                 }
//                 Err(err) => {
//                     writeln!(f, "ERROR at {:04}: {}", offset, err)?;
//                     offset += 1;
//                 }
//             }
//         }
//         Ok(())
//     }
// }

// impl Deref for Instructions {
//     type Target = [u8];

//     fn deref(&self) -> &[u8] {
//         &self.0
//     }
// }

// impl<'a> IntoIterator for &'a Instructions {
//     type Item = &'a u8;
//     type IntoIter = std::slice::Iter<'a, u8>;

//     fn into_iter(self) -> Self::IntoIter {
//         self.0.iter()
//     }
// }

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

        let tests = [TestCase::new(
            OpCodeKind::Constant,
            &[0xfffe],
            &[OpCodeKind::Constant as u8, 0xff, 0xfe],
        )];

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
    //     fn test_instructions_string() {
    //         let mut insts = Instructions::new();
    //         insts.add_inst(&Instruction::new(OpCodeKind::Add, &[]).unwrap());
    //         insts.add_inst(&Instruction::new(OpCodeKind::Constant, &[2]).unwrap());
    //         insts.add_inst(&Instruction::new(OpCodeKind::Constant, &[65535]).unwrap());

    //         let expected = "\
    // 0000 OpAdd
    // 0001 OpConstant 2
    // 0004 OpConstant 65535
    // ";
    //         assert_eq!(insts.to_string(), expected);
    //     }

    //     #[test]
    //     fn test_wrong_operand_count() {
    //         assert!(Instruction::new(OpCodeKind::Constant, &[]).is_err());
    //         assert!(Instruction::new(OpCodeKind::Constant, &[1, 2]).is_err());
    //     }
}
