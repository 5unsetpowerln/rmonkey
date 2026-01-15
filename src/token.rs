use crate::enum_with_static_str;

enum_with_static_str! {
    pub enum TokenKind {
        Illegal => "ILLEGAL",
        Eof     => "EOF",

        // Identifiers + literals
        Ident => "IDENT", // add, foobar, x, y, ...
        Int   => "INT",   // 1343456

        // Operators
        Assign   => "=",
        Plus     => "+",

        // Delimiters
        Comma     => ",",
        Semicolon => ";",

        LParen => "(",
        RParen => ")",
        LBrace => "{",
        RBrace => "}",

        // Keywords
        Function => "FUNCTION",
        Let      => "LET"

    }
}

pub struct Token {
    pub kind: TokenKind,
    pub literal: String,
}
