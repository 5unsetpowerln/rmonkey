use std::collections::HashMap;
use std::fmt;
use std::ops::Deref;
use std::sync::LazyLock;

use anyhow::{Context, Result, bail, ensure};
use thiserror::Error;

use crate::utils::push_u16_to_bytes_big_endian;

#[derive(Debug, Error)]
pub enum CodeError {
    #[error("definition for opcode `{opcode:?}` not found.")]
    DefinitionNotFound { opcode: OpCode },
    #[error("wrong number of operand for opcode `{opcode:?}`. got: {got}, expected: {expected}")]
    WrongNumberOfOperand {
        opcode: OpCode,
        expected: usize,
        got: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Instructions(Vec<u8>);

impl Instructions {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn from_list(insts_list: &[Instructions]) -> Self {
        let total: usize = insts_list.iter().map(|i| i.0.len()).sum();
        let mut buf = Vec::with_capacity(total);
        for insts in insts_list {
            buf.extend_from_slice(&insts.0);
        }
        Self(buf)
    }

    fn from_slice(slice: &[u8]) -> Self {
        Self(slice.to_vec())
    }

    pub fn emit(&mut self, bytes: &[u8]) -> usize {
        let pos = self.0.len();
        self.0.extend_from_slice(bytes);
        pos
    }

    pub fn push_u8(&mut self, value: u8) -> usize {
        let pos = self.0.len();
        self.0.push(value);
        pos
    }

    pub fn push_u16_big_endian(&mut self, value: u16) -> usize {
        let pos = self.0.len();
        self.0.extend_from_slice(&value.to_be_bytes());
        pos
    }

    pub fn push_u32_big_endian(&mut self, value: u32) -> usize {
        let pos = self.0.len();
        self.0.extend_from_slice(&value.to_be_bytes());
        pos
    }

    pub fn push_u64_big_endian(&mut self, value: u64) -> usize {
        let pos = self.0.len();
        self.0.extend_from_slice(&value.to_be_bytes());
        pos
    }

    pub fn read_u8_big_endian(&self, offset: usize) -> u8 {
        u8::from_be_bytes(self[offset..offset + 1].try_into().unwrap())
    }

    pub fn read_u16_big_endian(&self, offset: usize) -> u16 {
        u16::from_be_bytes(self[offset..offset + 2].try_into().unwrap())
    }

    pub fn read_u32_big_endian(&self, offset: usize) -> u32 {
        u32::from_be_bytes(self[offset..offset + 4].try_into().unwrap())
    }

    pub fn read_u64_big_endian(&self, offset: usize) -> u64 {
        u64::from_be_bytes(self[offset..offset + 8].try_into().unwrap())
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    // オペランドとオペランドが合計で何バイト幅なのかを返す
    pub fn read_operands(&self, opcode_def: &OpCodeDefinition) -> (Vec<u64>, usize) {
        let mut operands = Vec::new();
        let mut offset = 0;

        for width in opcode_def.operand_widths.iter() {
            match width {
                2 => operands.push(self.read_u16_big_endian(offset) as u64),
                _ => unimplemented!(),
            }

            offset += width;
        }

        (operands, offset)
    }
}

impl fmt::Display for Instructions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut i = 0;
        while i < self.0.len() {
            let opcode = match OpCode::from_u8(self.0[i]) {
                Some(op) => op,
                None => {
                    writeln!(f, "ERROR: unknown opcode: {}", self.0[i])?;
                    continue;
                }
            };

            let opcode_def = match OpCodeDefinition::lookup(opcode) {
                Ok(def) => def,
                Err(err) => {
                    writeln!(f, "ERROR: {}", err)?;
                    continue;
                }
            };

            let (operands, read) =
                Instructions::from_slice(&self[i + 1..]).read_operands(&opcode_def);

            writeln!(
                f,
                "{:04} {}",
                i,
                fmt_instruction(self, &opcode_def, &operands)
            )?;

            i += 1 + read;
        }
        Ok(())
    }
}

fn fmt_instruction(
    instructions: &Instructions,
    opcode_def: &OpCodeDefinition,
    operands: &[u64],
) -> String {
    let operand_count = opcode_def.operand_widths.len();

    if operands.len() != operand_count {
        return format!(
            "ERROR: wrong operand length. expected: {}, got: {}.",
            operand_count,
            operands.len()
        );
    }

    match operand_count {
        1 => {
            return format!("{} {}", opcode_def.name, operands[0]);
        }
        _ => {}
    }

    format!("ERROR: unhandled operand count for {}.", opcode_def.name)
}

// operandCount := len(def.OperandWidths)

// if len(operands) != operandCount {
//         len(operands), operandCount)
// }

// switch operandCount {
// case 1:
//     return fmt.Sprintf("%s %d", def.Name, operands[0])
// }

// return fmt.Sprintf("ERROR: unhandled operandCount for %s\n", def.Name)

// impl From<&[u8]> for Instructions {
//     fn from(slice: &[u8]) -> Self {
//         Self(slice.to_vec())
//     }
// }

impl Deref for Instructions {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.0
    }
}

impl<'a> IntoIterator for &'a Instructions {
    type Item = &'a u8;
    type IntoIter = std::slice::Iter<'a, u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[repr(u8)]
pub enum OpCode {
    Constant,
}

impl OpCode {
    pub fn from_u8(byte: u8) -> Option<Self> {
        match byte {
            b if b == Self::Constant as u8 => Some(Self::Constant),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct OpCodeDefinition {
    pub name: String,
    pub operand_widths: Vec<usize>,
}

impl OpCodeDefinition {
    pub fn new(name: &str, operand_widths: &[usize]) -> Self {
        Self {
            name: name.to_string(),
            operand_widths: operand_widths.to_vec(),
        }
    }

    pub fn lookup(opcode: OpCode) -> Result<Self> {
        match DEFINITIONS.get(&opcode) {
            Some(def) => Ok(def.clone()),
            None => bail!(CodeError::DefinitionNotFound { opcode }),
        }
    }
}

// // オペランドとオペランドが合計で何バイト幅なのかを返す
// pub fn read_operands(def: &Definition, instructions: Instructions) -> (Vec<u64>, usize) {

// }

static DEFINITIONS: LazyLock<HashMap<OpCode, OpCodeDefinition>> = LazyLock::new(|| {
    let mut map = HashMap::new();

    map.insert(OpCode::Constant, OpCodeDefinition::new("OpConstant", &[2]));

    map
});

// operandの幅は別に64bitじゃなくても、この関数に渡すときは64bitとして渡す (とりあえず)
pub fn create_inst(opcode: OpCode, operands: &[u64]) -> Result<Instructions> {
    let def = OpCodeDefinition::lookup(opcode)
        .with_context(|| format!("failed to lookup definition for the opcode: `{:?}`", opcode))?;

    ensure!(
        operands.len() == def.operand_widths.len(),
        CodeError::WrongNumberOfOperand {
            opcode,
            expected: def.operand_widths.len(),
            got: operands.len()
        }
    );

    let mut instructions = Instructions::new();

    instructions.push_u8(opcode as u8);

    for (i, operand) in operands.iter().enumerate() {
        let width = def.operand_widths[i];

        match width {
            2 => {
                instructions.push_u16_big_endian(*operand as u16);
            }
            _ => {
                unimplemented!()
            }
        }
    }

    Ok(instructions)
}

mod test {
    use crate::code::{OpCode, OpCodeDefinition, create_inst};
    use crate::utils::{concatenate_insts_list, print_errors};

    use super::Instructions;

    #[test]
    fn test_make() {
        struct Test {
            opcode: OpCode,
            operands: Vec<u64>,
            expected: Vec<u8>,
        }
        impl Test {
            fn new(opcode: OpCode, operands: &[u64], expected: &[u8]) -> Self {
                Self {
                    opcode,
                    operands: operands.to_vec(),
                    expected: expected.to_vec(),
                }
            }
        }

        let tests = vec![Test::new(
            OpCode::Constant,
            &[0xfffe],
            &[OpCode::Constant as u8, 0xff, 0xfe],
        )];

        for (i, test) in tests.iter().enumerate() {
            let inst = create_inst(test.opcode, &test.operands).unwrap_or_else(|err| {
                print_errors("failed to create an instruction", err);
                panic!();
            });

            if inst.len() != test.expected.len() {
                panic!(
                    "test {} failed. instruction has wrong length. expected: {}, got: {}.",
                    i,
                    test.expected.len(),
                    inst.len()
                );
            }

            for (j, byte) in inst.iter().enumerate() {
                if *byte != test.expected[j] {
                    panic!(
                        "test {} failed. wrong byte at pos {}. expected: {}, got: {}",
                        i, j, test.expected[j], inst[j]
                    );
                }
            }
        }
    }

    #[test]
    fn test_instructions_string() {
        let instructions = Instructions::from_list(&[
            create_inst(OpCode::Constant, &[1]).unwrap(),
            create_inst(OpCode::Constant, &[2]).unwrap(),
            create_inst(OpCode::Constant, &[65535]).unwrap(),
        ]);

        let expected = "0000 OpConstant 1
0003 OpConstant 2
0006 OpConstant 65535
";

        if instructions.to_string() != expected.to_string() {
            panic!(
                "instructions wrongly formatted. expected: {:?}, got: {:?}",
                expected,
                instructions.to_string()
            );
        }
    }

    #[test]
    fn test_read_operands() {
        struct Test {
            opcode: OpCode,
            operands: Vec<u64>,
            bytes_read: usize,
        }

        impl Test {
            fn new(opcode: OpCode, operands: &[u64], bytes_read: usize) -> Self {
                Self {
                    opcode,
                    operands: operands.to_vec(),
                    bytes_read,
                }
            }
        }

        let tests = [Test::new(OpCode::Constant, &[65535], 2)];

        for (i, test) in tests.iter().enumerate() {
            let instructions = create_inst(test.opcode, &test.operands).unwrap_or_else(|err| {
                print_errors(
                    format!("test {} failed. failed to create an instructions.", i).as_str(),
                    err,
                );
                panic!();
            });

            let opcode_raw = instructions.read_u8_big_endian(0);
            let opcode = OpCode::from_u8(opcode_raw).unwrap_or_else(|| {
                panic!("unknown opcode: {}", opcode_raw);
            });

            let opcode_def = OpCodeDefinition::lookup(opcode).unwrap_or_else(|err| {
                print_errors(
                    format!(
                        "test {} failed. failed to lookup definition for opcode: {:?}.",
                        i, opcode,
                    )
                    .as_str(),
                    err,
                );
                panic!();
            });

            let (operands, size) =
                Instructions::from_slice(&instructions[1..]).read_operands(&opcode_def);

            if size != test.bytes_read {
                panic!(
                    "test {} failed. wrong size of operands. expected: {}, got: {}.",
                    i, test.bytes_read, size
                );
            }

            for (j, operand) in operands.iter().enumerate() {
                if *operand != test.operands[j] {
                    panic!(
                        "test {} failed. operand at {} is wrong. expected: {}, got: {}.",
                        i, j, test.operands[j], operand
                    );
                }
            }
        }

        // for _, tt := range tests {
        //        instruction := Make(tt.op, tt.operands...)

        //        def, err := Lookup(byte(tt.op))
        //        if err != nil {
        //            t.Fatalf("definition not found: %q\n", err)
        //        }

        //        operandsRead, n := ReadOperands(def, instruction[1:])
        //        if n != tt.bytesRead {
        //            t.Fatalf("n wrong. want=%d, got=%d", tt.bytesRead, n)
        //        }

        //        for i, want := range tt.operands {
        //            if operandsRead[i] != want {
        //                t.Errorf("operand wrong. want=%d, got=%d", want, operandsRead[i])
        //            }
        //        }
        //    }
    }
}
