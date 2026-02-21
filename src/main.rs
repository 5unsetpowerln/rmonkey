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

use std::cell::RefCell;
use std::io::Read;
use std::os::unix::fs::MetadataExt;
use std::path::PathBuf;
use std::rc::Rc;

use clap::Parser;

use self::eval::eval;
use self::lexer::Lexer;
use self::object::Environment;

#[derive(clap::Parser, Debug)]
struct Args {
    #[arg(short, long)]
    input: Option<PathBuf>,
}

fn main() {
    let args = Args::parse();

    match &args.input {
        Some(input_file_path) => {
            let file = std::fs::File::open(input_file_path).expect("failed to open the file.");
            let metadata = file
                .metadata()
                .expect("failed to get the metadata of the file.");
            let mut reader = std::io::BufReader::new(file);

            let mut input = String::new();

            let read_size = reader
                .read_to_string(&mut input)
                .expect("failed to read the file.");
            if metadata.size() as usize != read_size {
                panic!("file size and read size is not equal.");
            }

            let mut lexer = Lexer::new(&input);
            let mut parser = parser::Parser::new(&mut lexer);
            let program = parser
                .parse_program()
                .expect("failed to parse the program.");
            let environment = Rc::new(RefCell::new(Environment::new(None)));
            let evaluated = eval(&program, environment).expect("failed to eval the program.");
            if let Some(value) = evaluated {
                println!("{}", value.as_ref());
            }
        }
        _ => {
            repl::start();
        }
    }
}
