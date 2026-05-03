use std::io::{Write, stdin, stdout};
use std::sync::Arc;

use crate::compiler::Compiler;
use crate::lexer::Lexer;
use crate::object::{Environment, Object};
use crate::parser::Parser;
use crate::symbol_table;
use crate::utils::print_errors;
use crate::vm::{self, Vm};

const PROMPT: &str = ">> ";

pub fn start() {
    println!("Hello. This is the rMonkey programming language!");
    println!("Feel free to type in commands");

    let stdin_ = stdin();
    let mut stdout_ = stdout();

    let mut globals = (0..vm::GLOBAL_SIZE)
        .map(|_| None)
        .collect::<Vec<Option<Arc<Object>>>>()
        .to_vec();
    let mut symbol_table = symbol_table::SymbolTable::new();
    let mut constants = Vec::new();

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

        let mut compiler = Compiler::new_with_state(&symbol_table, &constants);
        if let Err(err) = compiler.compile(&program) {
            print_errors("failed to compile the program", err);
            continue;
        }

        let bytecode = compiler.get_bytecode();

        symbol_table = compiler.get_symbol_table();
        constants = bytecode.constants.clone();

        let mut vm = Vm::new_with_global_store(&bytecode, &globals);
        if let Err(err) = vm.run() {
            print_errors("failed to run the program on the vm", err);
            continue;
        }

        globals = vm.get_globals();

        if let Some(last_stack_top) = vm.last_stack_top() {
            println!("{}", last_stack_top.as_ref());
        }
    }
}
