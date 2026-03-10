use std::rc::Rc;

use anyhow::Result;

use crate::code::Instructions;
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

    pub fn compile<T: ast::NodeInterface>(&mut self, node: &T) -> Result<()> {
        todo!()
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
    use std::mem::discriminant;
    use std::rc::Rc;

    use anyhow::{Context, Result, bail};

    use crate::ast::Program;
    use crate::code::{OpCode, create_inst};
    use crate::compiler::Compiler;
    use crate::lexer::Lexer;
    use crate::object::Object;
    use crate::parser::Parser;
    use crate::utils::{concatenate_insts_list, print_errors};

    use super::Instructions;

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
            let expected_instructions = Instructions::from_list(expected_instructions);

            Self {
                input: input.to_string(),
                expected_constants: expected_constants.to_vec(),
                expected_instructions,
            }
        }
    }

    #[test]
    fn test_integer_arithmetic() {
        let tests = [CompilerTestCase::new(
            "1 + 2",
            &[Object::int(1), Object::int(2)],
            &[
                create_inst(OpCode::Constant, &[0]).unwrap(),
                create_inst(OpCode::Constant, &[1]).unwrap(),
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
                    format!("test {} failed. failed to test instructions.", i).as_str(),
                    err,
                );
                panic!();
            });

            test_consts(&test.expected_constants, &bytecode.constants).unwrap_or_else(|err| {
                print_errors(
                    format!("test {} failed. failed to test constants.", i).as_str(),
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

    fn test_insts(expected_insts: &Instructions, actual_insts: &Instructions) -> Result<()> {
        if expected_insts.len() != actual_insts.len() {
            bail!(
                "wrong instructions length. expected: {}, got: {}.",
                expected_insts.len(),
                actual_insts.len()
            );
        }

        for (i, expceted_byte) in expected_insts.iter().enumerate() {
            if actual_insts[i] != *expceted_byte {
                bail!(
                    "wrong instruction at {}. expected: {}, got: {}.",
                    i,
                    expceted_byte,
                    actual_insts[i]
                );
            }
        }

        Ok(())
    }

    fn test_consts(expected_constants: &[Object], actual: &[Rc<Object>]) -> Result<()> {
        if expected_constants.len() != actual.len() {
            bail!(
                "wrong number of constants. got: {}, expected: {}.",
                actual.len(),
                expected_constants.len()
            );
        }

        for (i, expected_constant) in expected_constants.iter().enumerate() {
            match expected_constant {
                Object::Integer(int_obj) => {
                    test_integer_object(int_obj.borrow().value, &actual[i]).with_context(|| {
                        format!("test {} failed. failed to test integer object", i)
                    })?;
                }
                _ => {
                    unimplemented!()
                }
            }
        }

        Ok(())
    }

    fn test_integer_object(expected: i64, actual: &Object) -> Result<()> {
        match actual {
            Object::Integer(integer_object) => {
                if integer_object.borrow().value != expected {
                    bail!(
                        "the object has wrong value. expected: {}, got: {}.",
                        expected,
                        integer_object.borrow().value
                    );
                }
            }
            other => {
                bail!("the object is not IntegerObject. got: {}", other)
            }
        }

        Ok(())
    }
}
