use std::io::{Write, stdin, stdout};

use crate::ast::NodeInterface;
use crate::eval::eval;
use crate::lexer::Lexer;
use crate::object::Environment;
use crate::parser::Parser;
use crate::utils::print_errors;

const PROMPT: &str = ">> ";

pub fn start() {
    let stdin_ = stdin();
    let mut stdout_ = stdout();

    let mut environment = Environment::new();

    loop {
        print!("{PROMPT}");
        stdout_.flush().expect("failed to flush stdout");

        let mut line = String::new();

        let _read_size = stdin_
            .read_line(&mut line)
            .expect("falied to read a line from stdin.");

        let mut lexer = Lexer::new(line.as_ascii().expect("failed to parse an input as ascii"));
        let mut parser = Parser::new(&mut lexer);

        let program = if let Ok(p) = parser.parse_program() {
            p
        } else {
            parser.print_errors();
            println!("failed to parse.");
            continue;
        };

        let evaluated = match eval(&program, &mut environment) {
            Ok(x) => x,
            Err(err) => {
                print_errors("failed to evaluate the program", err);
                continue;
            }
        };

        println!("{evaluated}");
    }
}
