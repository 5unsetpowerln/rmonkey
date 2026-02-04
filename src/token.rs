use core::ascii;
use std::fmt::{Debug, Display};

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub enum TokenKind {
    Illegal,
    Eof,

    // Identifiers + literals
    Ident,
    Int,

    // Operators
    Assign,
    Plus,
    Minus,
    Exclamation,
    Asterisk,
    Slash,

    LessThan,
    GreaterThan,

    Eq,
    NotEq,

    // Delimiters
    Comma,
    Semicolon,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,

    // Keywords
    Function,
    Let,
    True,
    False,
    If,
    Else,
    Return,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub literal: Vec<ascii::Char>,
}

impl Token {
    pub fn new(kind: TokenKind, literal: &[ascii::Char]) -> Self {
        Self {
            kind,
            literal: literal.to_vec(),
        }
    }

    pub fn empty() -> Self {
        Self {
            kind: TokenKind::Illegal,
            literal: Vec::new(),
        }
    }
}
