#![feature(ascii_char)]
#![feature(ascii_char_variants)]

use self::lexer::Lexer;
use self::token::TokenKind;

mod lexer;
mod repl;
mod token;
mod utils;

fn main() {
    env_logger::init();

    println!("Hello. This is the rMonkey programming language!");
    println!("Feel free to type in commands");

    repl::start();
}
