use std::cell::RefCell;
use std::io::{Write, stdin, stdout};
use std::rc::Rc;

use crate::eval::eval;
use crate::lexer::Lexer;
use crate::object::Environment;
use crate::parser::Parser;
use crate::utils::print_errors;

const PROMPT: &str = ">> ";

pub fn start() {
    println!("Hello. This is the rMonkey programming language!");
    println!("Feel free to type in commands");

    let stdin_ = stdin();
    let mut stdout_ = stdout();

    let env = Rc::new(RefCell::new(Environment::new(None)));

    loop {
        print!("{PROMPT}");
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

        let evaluated = match eval(&program, env.clone()) {
            Ok(x) => x,
            Err(err) => {
                print_errors("failed to evaluate the program", err);
                continue;
            }
        };

        if let Some(value) = evaluated {
            println!("{}", value)
        }
    }
}
