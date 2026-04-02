use std::fmt;

use anyhow::{Result, bail};

use crate::code::{OpCodeDef, OpCodeKind};

pub fn disasm(insts: &[u8]) -> String {
    let insts = Instructions(insts.to_vec());
    insts.to_string()
}

// Instruction
#[derive(Debug, Clone)]
struct Instruction {
    pub opcode: &'static OpCodeDef,
    pub operands: Vec<u64>,
}

impl Instruction {
    pub fn read_from(bytes: &[u8], offset: usize) -> Result<(Self, usize)> {
        let opcode = OpCodeDef::lookup_byte(bytes[offset])?;
        let mut operands = Vec::with_capacity(opcode.operand_widths.len());
        let mut pos = offset + 1;

        for &width in opcode.operand_widths {
            let operand = match width {
                1 => bytes[pos] as u64,
                2 => u16::from_be_bytes(bytes[pos..pos + 2].try_into().unwrap()) as u64,
                4 => u32::from_be_bytes(bytes[pos..pos + 4].try_into().unwrap()) as u64,
                8 => u64::from_be_bytes(bytes[pos..pos + 8].try_into().unwrap()),
                w => unimplemented!("operand width {} not supported", w),
            };
            operands.push(operand);
            pos += width;
        }

        let bytes_read = pos - offset;
        Ok((Self { opcode, operands }, bytes_read))
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.opcode.name)?;
        for operand in &self.operands {
            write!(f, " {}", operand)?;
        }
        Ok(())
    }
}

// Instructions
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Instructions(pub Vec<u8>);

impl Instructions {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn from_inst_list(list: &[Instructions]) -> Self {
        let total: usize = list.iter().map(|i| i.0.len()).sum();
        let mut buf = Vec::with_capacity(total);
        for insts in list {
            buf.extend_from_slice(&insts.0);
        }
        Self(buf)
    }
}

impl fmt::Display for Instructions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut offset = 0;
        while offset < self.0.len() {
            match Instruction::read_from(&self.0, offset) {
                Ok((inst, bytes_read)) => {
                    writeln!(f, "{:04} {}", offset, inst)?;
                    offset += bytes_read;
                }
                Err(err) => {
                    writeln!(f, "ERROR at {:04}: {}", offset, err)?;
                    offset += 1;
                }
            }
        }
        Ok(())
    }
}
