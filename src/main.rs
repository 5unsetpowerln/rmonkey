#![feature(ascii_char)]
#![feature(ascii_char_variants)]

mod ast;
mod builtins;
mod eval;
mod lexer;
mod object;
mod parser;
mod repl;
mod token;
mod utils;

fn main() {
    println!("Hello. This is the rMonkey programming language!");
    println!("Feel free to type in commands");

    repl::start();
}
