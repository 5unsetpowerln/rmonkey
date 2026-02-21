use core::ascii;
use std::fmt::{self, Debug, Display};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Illegal,
    Eof,

    // Identifiers + literals
    Ident,
    Int,
    String,

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
    LeftBracket,
    RightBracket,
    Colon,

    // Keywords
    Function,
    Let,
    True,
    False,
    If,
    Else,
    Return,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            // Identifiers + literals
            TokenKind::Ident => "identifier",
            TokenKind::Int => "integer",
            TokenKind::String => "string",

            // Operators
            TokenKind::Assign => "`=`",
            TokenKind::Plus => "`+`",
            TokenKind::Minus => "`-`",
            TokenKind::Exclamation => "`!`",
            TokenKind::Asterisk => "`*`",
            TokenKind::Slash => "`/`",
            TokenKind::LessThan => "`<`",
            TokenKind::GreaterThan => "`>`",
            TokenKind::Eq => "`==`",
            TokenKind::NotEq => "`!=`",

            // Delimiters
            TokenKind::Comma => "`,`",
            TokenKind::Semicolon => "`;`",
            TokenKind::LeftParen => "`(`",
            TokenKind::RightParen => "`)`",
            TokenKind::LeftBrace => "`{`",
            TokenKind::RightBrace => "`}`",
            TokenKind::LeftBracket => "`[`",
            TokenKind::RightBracket => "`]`",
            TokenKind::Colon => "`:`",

            // Keywords
            TokenKind::Function => "`fn`",
            TokenKind::Let => "`let`",
            TokenKind::True => "`true`",
            TokenKind::False => "`false`",
            TokenKind::If => "`if`",
            TokenKind::Else => "`else`",
            TokenKind::Return => "`return`",

            // Special
            TokenKind::Eof => "end of file",
            TokenKind::Illegal => "illegal token",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub literal: String,
}

impl Token {
    pub fn new(kind: TokenKind, literal: &str) -> Self {
        Self {
            kind,
            literal: literal.to_string(),
        }
    }

    pub fn empty() -> Self {
        Self {
            kind: TokenKind::Illegal,
            literal: String::new(),
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            // literal が実質的な値である場合はその情報も含める
            TokenKind::Ident | TokenKind::Int | TokenKind::String => {
                write!(f, "{} `{}`", self.kind, self.literal.as_str())
            }
            _ => write!(f, "{}", self.kind),
        }
    }
}
