use std::io::{Write, stdin, stdout};

use crate::lexer::Lexer;
use crate::token::TokenKind;

const PROMPT: &str = ">> ";

pub fn start() {
    let stdin_ = stdin();
    let mut stdout_ = stdout();

    loop {
        print!("{PROMPT}");
        stdout_.flush().expect("failed to flush stdout");

        let mut line = String::new();

        let _read_size = stdin_
            .read_line(&mut line)
            .expect("falied to read a line from stdin.");

        let mut lexer = Lexer::new(line.as_ascii().expect("failed to parse an input as ascii"));

        loop {
            let token = lexer.next_token();
            if token.kind == TokenKind::Eof {
                break;
            }

            println!("{token:?}");
        }
    }
}
