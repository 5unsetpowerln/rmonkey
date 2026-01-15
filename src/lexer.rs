use crate::token::Token;

pub struct Lexer {
    input: String,
    position: usize,      // current position in input (points to current char)
    read_position: usize, // current reading position in input (after current char)
    c: char,              // current char under examination
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        Self {
            input: input.to_string(),
            position: 0,
            read_position: 0,
            c: unsafe { char::from_u32_unchecked(0) },
        }
    }

    pub fn next_token(&mut self) -> Token {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use log::error;

    use crate::lexer::Lexer;
    use crate::token::TokenKind;

    #[test]
    fn test_next_token() {
        let input = "=+(){},;";

        struct Test {
            pub expected_kind: TokenKind,
            pub expected_literal: String,
        }

        impl Test {
            fn new(kind: TokenKind, literal: &str) -> Self {
                Self {
                    expected_kind: kind,
                    expected_literal: literal.to_string(),
                }
            }
        }

        let tests = vec![
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Plus, "+"),
            Test::new(TokenKind::LParen, "("),
            Test::new(TokenKind::RParen, ")"),
            Test::new(TokenKind::LBrace, "{"),
            Test::new(TokenKind::RBrace, "}"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Eof, ""),
        ];

        let mut lexer = Lexer::new(input);

        for (i, t) in tests.iter().enumerate() {
            let token = lexer.next_token();

            if t.expected_kind != token.kind {
                error!(
                    "tests[{}] - tokenkind wrong. expected={}, got={}",
                    i, t.expected_kind, token.kind
                );
                panic!();
            }

            if *token.literal != *t.expected_literal {
                error!(
                    "tests[{}] - literal wrong. expected={}, got={}",
                    t.expected_literal, token.literal
                );
            }
        }
    }
}
