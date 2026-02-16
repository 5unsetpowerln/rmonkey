use core::ascii;

use crate::token::{Token, TokenKind};

#[derive(Debug)]
pub struct Lexer {
    input: Vec<ascii::Char>,
    position: usize,      // current position in input (points to current char)
    read_position: usize, // current reading position in input (after current char)
    c: ascii::Char,       // current char under examination
}

impl Lexer {
    pub fn new(input: &[ascii::Char]) -> Self {
        let mut self_ = Self {
            input: input.to_vec(),
            position: 0,
            read_position: 0,
            c: ascii::Char::Null,
        };

        self_.read_char();

        self_
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let token = match self.c {
            ascii::Char::Null => Token::new(TokenKind::Eof, &[ascii::Char::Null]),
            ascii::Char::EqualsSign => {
                if self.peek_char() == ascii::Char::EqualsSign {
                    self.read_char();
                    Token::new(TokenKind::Eq, unsafe { "==".as_ascii_unchecked() })
                } else {
                    Token::new(TokenKind::Assign, unsafe { "=".as_ascii_unchecked() })
                }
            }
            ascii::Char::PlusSign => {
                Token::new(TokenKind::Plus, unsafe { "+".as_ascii_unchecked() })
            }
            ascii::Char::HyphenMinus => {
                Token::new(TokenKind::Minus, unsafe { "-".as_ascii_unchecked() })
            }
            ascii::Char::ExclamationMark => {
                if self.peek_char() == ascii::Char::EqualsSign {
                    self.read_char();
                    Token::new(TokenKind::NotEq, unsafe { "!=".as_ascii_unchecked() })
                } else {
                    Token::new(TokenKind::Exclamation, unsafe { "!".as_ascii_unchecked() })
                }
            }
            ascii::Char::Asterisk => {
                Token::new(TokenKind::Asterisk, unsafe { "*".as_ascii_unchecked() })
            }
            ascii::Char::Solidus => {
                Token::new(TokenKind::Slash, unsafe { "/".as_ascii_unchecked() })
            }
            ascii::Char::LessThanSign => {
                Token::new(TokenKind::LessThan, unsafe { "<".as_ascii_unchecked() })
            }
            ascii::Char::GreaterThanSign => {
                Token::new(TokenKind::GreaterThan, unsafe { ">".as_ascii_unchecked() })
            }
            ascii::Char::Comma => Token::new(TokenKind::Comma, unsafe { ",".as_ascii_unchecked() }),
            ascii::Char::Semicolon => {
                Token::new(TokenKind::Semicolon, unsafe { ";".as_ascii_unchecked() })
            }
            ascii::Char::LeftParenthesis => {
                Token::new(TokenKind::LeftParen, unsafe { "(".as_ascii_unchecked() })
            }
            ascii::Char::RightParenthesis => {
                Token::new(TokenKind::RightParen, unsafe { ")".as_ascii_unchecked() })
            }
            ascii::Char::LeftCurlyBracket => {
                Token::new(TokenKind::LeftBrace, unsafe { "{".as_ascii_unchecked() })
            }
            ascii::Char::RightCurlyBracket => {
                Token::new(TokenKind::RightBrace, unsafe { "}".as_ascii_unchecked() })
            }
            ascii::Char::QuotationMark => Token::new(TokenKind::String, &self.read_string()),
            _ => {
                if is_letter(self.c) {
                    // a~z/A~Z/_から始まる場合はidentifier/keywordとして解釈する
                    // read_identifiersがread_charを呼び出すので早期リターンする
                    return match self.read_identifiers().as_str() {
                        "fn" => {
                            Token::new(TokenKind::Function, unsafe { "fn".as_ascii_unchecked() })
                        }
                        "let" => Token::new(TokenKind::Let, unsafe { "let".as_ascii_unchecked() }),
                        "true" => {
                            Token::new(TokenKind::True, unsafe { "true".as_ascii_unchecked() })
                        }
                        "false" => {
                            Token::new(TokenKind::False, unsafe { "false".as_ascii_unchecked() })
                        }
                        "if" => Token::new(TokenKind::If, unsafe { "if".as_ascii_unchecked() }),
                        "else" => {
                            Token::new(TokenKind::Else, unsafe { "else".as_ascii_unchecked() })
                        }
                        "return" => {
                            Token::new(TokenKind::Return, unsafe { "return".as_ascii_unchecked() })
                        }
                        other => Token::new(
                            TokenKind::Ident,
                            other
                                .as_ascii()
                                .expect("failed to parse an identifier as ascii"),
                        ),
                    };
                } else if is_digit(self.c) {
                    // 0~9から始まる場合はINTとして解釈する
                    // read_numberがread_charを呼び出すので早期リターンする

                    return Token::new(TokenKind::Int, self.read_number());
                } else {
                    // それ以外はIllegal
                    Token::new(TokenKind::Illegal, &[self.c])
                }
            }
        };

        self.read_char();

        token
    }

    fn read_string(&mut self) -> Vec<ascii::Char> {
        let position = self.position + 1;

        loop {
            self.read_char();
            if self.c == ascii::Char::QuotationMark || self.c == ascii::Char::Null {
                break;
            }
        }

        self.input[position..self.position].to_vec()
    }

    fn read_char(&mut self) {
        if let Some(c) = self.input.get(self.read_position) {
            self.c = *c;
        } else {
            self.c = ascii::Char::Null;
        }

        self.position = self.read_position;
        self.read_position += 1;
    }

    fn read_identifiers(&mut self) -> &[ascii::Char] {
        let position = self.position;
        while is_letter(self.c) {
            self.read_char();
        }

        self.input.get(position..self.position).unwrap()
    }

    fn skip_whitespace(&mut self) {
        while self.c == ascii::Char::Space
            || self.c == ascii::Char::CharacterTabulation
            || self.c == ascii::Char::LineFeed
            || self.c == ascii::Char::CarriageReturn
        {
            self.read_char();
        }
    }

    fn read_number(&mut self) -> &[ascii::Char] {
        let position = self.position;
        while is_digit(self.c) {
            self.read_char();
        }

        self.input.get(position..self.position).unwrap()
    }

    fn peek_char(&mut self) -> ascii::Char {
        if self.read_position >= self.input.len() {
            return ascii::Char::Null;
        }

        self.input[self.read_position]
    }
}

fn is_letter(c: ascii::Char) -> bool {
    (ascii::Char::SmallA..=ascii::Char::SmallZ).contains(&c)
        || (ascii::Char::CapitalA..ascii::Char::CapitalZ).contains(&c)
        || c == ascii::Char::LowLine
}

fn is_digit(c: ascii::Char) -> bool {
    (ascii::Char::Digit0..=ascii::Char::Digit9).contains(&c)
}

#[cfg(test)]
mod test {
    use core::ascii;
    use log::{error, info};

    use crate::lexer::Lexer;
    use crate::token::TokenKind;

    struct Test {
        pub expected_kind: TokenKind,
        pub expected_literal: Vec<ascii::Char>,
    }

    impl Test {
        // literalに渡される文字列がascii文字列であることを仮定している
        fn new(kind: TokenKind, literal: &str) -> Self {
            Self {
                expected_kind: kind,
                expected_literal: literal.as_ascii().unwrap().to_vec(),
            }
        }
    }

    #[test]
    fn test_next_token1() {
        let input = "
            let five = 5;
            let ten = 10;

            let add = fn(x, y) {
              x + y;
            };

            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;

            if (5 < 10) {
                return true;
            } else {
                return false;
            }

            10 == 10;
            10 != 9;
            \"foobar\"
            \"foo bar\"
            "
        .as_ascii()
        .unwrap();

        let tests = vec![
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "five"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "ten"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "add"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Function, "fn"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Ident, "x"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Ident, "y"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Ident, "x"),
            Test::new(TokenKind::Plus, "+"),
            Test::new(TokenKind::Ident, "y"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "result"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Ident, "add"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Ident, "five"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Ident, "ten"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Exclamation, "!"),
            Test::new(TokenKind::Minus, "-"),
            Test::new(TokenKind::Slash, "/"),
            Test::new(TokenKind::Asterisk, "*"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::LessThan, "<"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::GreaterThan, ">"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::If, "if"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::LessThan, "<"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Return, "return"),
            Test::new(TokenKind::True, "true"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Else, "else"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Return, "return"),
            Test::new(TokenKind::False, "false"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::Eq, "=="),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::NotEq, "!="),
            Test::new(TokenKind::Int, "9"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::String, "foobar"),
            Test::new(TokenKind::String, "foo bar"),
            Test::new(TokenKind::Eof, "\0"),
        ];

        let mut lexer = Lexer::new(input);

        for (i, t) in tests.iter().enumerate() {
            let token = lexer.next_token();

            if t.expected_kind != token.kind {
                panic!(
                    "tests[{}] - tokenkind wrong. expected={:?}, got={:?}",
                    i, t.expected_kind, token.kind
                );
            }

            if *token.literal != *t.expected_literal {
                panic!(
                    "tests[{}] - literal wrong. expected={:?}, got={:?}",
                    i, t.expected_literal, token.literal
                );
            }
        }
    }

    #[test]
    fn test_next_token2() {
        let input = "
            let five = 5;
            let ten = 10;

            let add = fn(x, y) {
            x + y;
            };

            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;"
            .as_ascii()
            .unwrap();

        let tests = vec![
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "five"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "ten"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "add"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Function, "fn"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Ident, "x"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Ident, "y"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Ident, "x"),
            Test::new(TokenKind::Plus, "+"),
            Test::new(TokenKind::Ident, "y"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "result"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Ident, "add"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Ident, "five"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Ident, "ten"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Exclamation, "!"),
            Test::new(TokenKind::Minus, "-"),
            Test::new(TokenKind::Slash, "/"),
            Test::new(TokenKind::Asterisk, "*"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::LessThan, "<"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::GreaterThan, ">"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Eof, "\0"),
        ];

        let mut lexer = Lexer::new(input);

        for (i, t) in tests.iter().enumerate() {
            let token = lexer.next_token();

            if t.expected_kind != token.kind {
                panic!(
                    "tests[{}] - tokenkind wrong. expected={:?}, got={:?}",
                    i, t.expected_kind, token.kind
                );
            }

            if *token.literal != *t.expected_literal {
                panic!(
                    "tests[{}] - literal wrong. expected={:?}, got={:?}",
                    i, t.expected_literal, token.literal
                );
            }
        }
    }

    #[test]
    fn test_next_token3() {
        let input = "
            let five = 5;
            let ten = 10;

            let add = fn(x, y) {
              x + y;
            };

            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;

            if (5 < 10) {
                return true;
            } else {
                return false;
            }
            "
        .as_ascii()
        .unwrap();

        let tests = vec![
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "five"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "ten"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "add"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Function, "fn"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Ident, "x"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Ident, "y"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Ident, "x"),
            Test::new(TokenKind::Plus, "+"),
            Test::new(TokenKind::Ident, "y"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "result"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Ident, "add"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Ident, "five"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Ident, "ten"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Exclamation, "!"),
            Test::new(TokenKind::Minus, "-"),
            Test::new(TokenKind::Slash, "/"),
            Test::new(TokenKind::Asterisk, "*"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::LessThan, "<"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::GreaterThan, ">"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::If, "if"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::LessThan, "<"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Return, "return"),
            Test::new(TokenKind::True, "true"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Else, "else"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Return, "return"),
            Test::new(TokenKind::False, "false"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Eof, "\0"),
        ];

        let mut lexer = Lexer::new(input);

        for (i, t) in tests.iter().enumerate() {
            let token = lexer.next_token();

            if t.expected_kind != token.kind {
                panic!(
                    "tests[{}] - tokenkind wrong. expected={:?}, got={:?}",
                    i, t.expected_kind, token.kind
                );
            }

            if *token.literal != *t.expected_literal {
                panic!(
                    "tests[{}] - literal wrong. expected={:?}, got={:?}",
                    i, t.expected_literal, token.literal
                );
            }
        }
    }

    #[test]
    fn test_next_token4() {
        let input = "
            let five = 5;
            let ten = 10;

            let add = fn(x, y) {
              x + y;
            };

            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;

            if (5 < 10) {
                return true;
            } else {
                return false;
            }

            10 == 10;
            10 != 9;
            "
        .as_ascii()
        .unwrap();

        let tests = vec![
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "five"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "ten"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "add"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Function, "fn"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Ident, "x"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Ident, "y"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Ident, "x"),
            Test::new(TokenKind::Plus, "+"),
            Test::new(TokenKind::Ident, "y"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Let, "let"),
            Test::new(TokenKind::Ident, "result"),
            Test::new(TokenKind::Assign, "="),
            Test::new(TokenKind::Ident, "add"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Ident, "five"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Ident, "ten"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Exclamation, "!"),
            Test::new(TokenKind::Minus, "-"),
            Test::new(TokenKind::Slash, "/"),
            Test::new(TokenKind::Asterisk, "*"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::LessThan, "<"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::GreaterThan, ">"),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::If, "if"),
            Test::new(TokenKind::LeftParen, "("),
            Test::new(TokenKind::Int, "5"),
            Test::new(TokenKind::LessThan, "<"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::RightParen, ")"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Return, "return"),
            Test::new(TokenKind::True, "true"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Else, "else"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::Return, "return"),
            Test::new(TokenKind::False, "false"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::RightBrace, "}"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::Eq, "=="),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Int, "10"),
            Test::new(TokenKind::NotEq, "!="),
            Test::new(TokenKind::Int, "9"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::Eof, "\0"),
        ];

        let mut lexer = Lexer::new(input);

        for (i, t) in tests.iter().enumerate() {
            let token = lexer.next_token();

            if t.expected_kind != token.kind {
                panic!(
                    "tests[{}] - tokenkind wrong. expected={:?}, got={:?}",
                    i, t.expected_kind, token.kind
                );
            }

            if *token.literal != *t.expected_literal {
                panic!(
                    "tests[{}] - literal wrong. expected={:?}, got={:?}",
                    i, t.expected_literal, token.literal
                );
            }
        }
    }
}
