use std::io::{Write, stdin, stdout};

use crate::compiler::Compiler;
use crate::eval::eval;
use crate::lexer::Lexer;
use crate::object::Environment;
use crate::parser::Parser;
use crate::utils::print_errors;
use crate::vm::Vm;

const PROMPT: &str = ">> ";

pub fn start() {
    println!("Hello. This is the rMonkey programming language!");
    println!("Feel free to type in commands");

    let stdin_ = stdin();
    let mut stdout_ = stdout();

    loop {
        print!("{}", PROMPT);
        stdout_.flush().expect("failed to flush stdout");

        let mut line = String::new();

        let _read_size = stdin_
            .read_line(&mut line)
            .expect("falied to read a line from stdin.");

        let mut lexer = Lexer::new(&line);
        let mut parser = Parser::new(&mut lexer);

        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(err) => {
                print_errors("failed to parse program", err);
                continue;
            }
        };

        let mut compiler = Compiler::new();
        if let Err(err) = compiler.compile(&program) {
            print_errors("failed to compile the program", err);
            continue;
        }

        let bytecode = compiler.get_bytecode();
        let mut vm = Vm::new(bytecode);
        if let Err(err) = vm.run() {
            print_errors("failed to run the program on the vm", err);
            continue;
        }

        if let Some(last_stack_top) = vm.last_stack_top() {
            println!("{}", last_stack_top.as_ref());
        }
    }
}
