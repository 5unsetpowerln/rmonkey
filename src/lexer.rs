use core::ascii;

use crate::token::{Token, TokenKind};

#[derive(Debug)]
pub struct Lexer {
    input: String,
    position: usize,      // current position in input (points to current char)
    read_position: usize, // current reading position in input (after current char)
    c: char,              // current char under examination
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        let mut self_ = Self {
            input: input.to_string(),
            position: 0,
            read_position: 0,
            c: ascii::Char::Null.to_char(),
        };

        self_.read_char();

        self_
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let token = match self.c {
            '\0' => Token::new(TokenKind::Eof, "\0"),
            '=' => {
                if self.peek_char() == '=' {
                    self.read_char();
                    Token::new(TokenKind::Eq, "==")
                } else {
                    Token::new(TokenKind::Assign, "=")
                }
            }
            '+' => Token::new(TokenKind::Plus, "+"),
            '-' => Token::new(TokenKind::Minus, "-"),
            '!' => {
                if self.peek_char() == '=' {
                    self.read_char();
                    Token::new(TokenKind::NotEq, "!=")
                } else {
                    Token::new(TokenKind::Exclamation, "!")
                }
            }
            '*' => Token::new(TokenKind::Asterisk, "*"),
            '/' => Token::new(TokenKind::Slash, "/"),
            '<' => Token::new(TokenKind::LessThan, "<"),
            '>' => Token::new(TokenKind::GreaterThan, ">"),
            ',' => Token::new(TokenKind::Comma, ","),
            ';' => Token::new(TokenKind::Semicolon, ";"),
            '(' => Token::new(TokenKind::LeftParen, "("),
            ')' => Token::new(TokenKind::RightParen, ")"),
            '{' => Token::new(TokenKind::LeftBrace, "{"),
            '}' => Token::new(TokenKind::RightBrace, "}"),
            '"' => Token::new(TokenKind::String, &self.read_string()),
            '[' => Token::new(TokenKind::LeftBracket, "["),
            ']' => Token::new(TokenKind::RightBracket, "]"),
            ':' => Token::new(TokenKind::Colon, ":"),
            _ => {
                if is_letter(self.c) {
                    // a~z/A~Z/_から始まる場合はidentifier/keywordとして解釈する
                    // read_identifiersがread_charを呼び出すので早期リターンする
                    match self.read_identifier().as_str() {
                        "fn" => {
                            return Token::new(TokenKind::Function, "fn");
                        }
                        "let" => {
                            return Token::new(TokenKind::Let, "let");
                        }
                        "true" => {
                            return Token::new(TokenKind::True, "true");
                        }
                        "false" => {
                            return Token::new(TokenKind::False, "false");
                        }
                        "if" => {
                            return Token::new(TokenKind::If, "if");
                        }
                        "else" => {
                            return Token::new(TokenKind::Else, "else");
                        }
                        "return" => {
                            return Token::new(TokenKind::Return, "return");
                        }
                        other => {
                            return Token::new(TokenKind::Ident, other);
                        }
                    };
                } else if is_digit(self.c) {
                    // 0~9から始まる場合はINTとして解釈する
                    // read_numberがread_charを呼び出すので早期リターンする

                    return Token::new(TokenKind::Int, self.read_number().as_str());
                } else {
                    // それ以外はIllegal
                    Token::new(TokenKind::Illegal, self.c.to_string().as_str())
                }
            }
        };

        self.read_char();

        token
    }

    fn read_string(&mut self) -> String {
        let position = self.position + 1;

        loop {
            self.read_char();
            if self.c == '"' || self.c == '\0' {
                break;
            }
        }

        self.input
            .chars()
            .skip(position)
            .take(self.position - position)
            .collect()
    }

    fn read_char(&mut self) {
        if let Some(c) = self.input.chars().nth(self.read_position) {
            self.c = c;
        } else {
            self.c = '\0';
        }

        self.position = self.read_position;
        self.read_position += 1;
    }

    fn read_identifier(&mut self) -> String {
        let position = self.position;

        while is_letter(self.c) {
            self.read_char();
        }

        self.input
            .chars()
            .skip(position)
            .take(self.position - position)
            .collect::<String>()
    }

    fn skip_whitespace(&mut self) {
        while self.c == ' ' || self.c == '\t' || self.c == '\n' || self.c == '\r' {
            self.read_char();
        }
    }

    fn read_number(&mut self) -> String {
        let position = self.position;
        while is_digit(self.c) {
            self.read_char();
        }

        self.input
            .chars()
            .skip(position)
            .take(self.position - position)
            .collect::<String>()
    }

    fn peek_char(&mut self) -> char {
        if self.read_position >= self.input.len() {
            return '\0';
        }

        self.input.chars().nth(self.read_position).unwrap()
    }
}

fn is_letter(c: char) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_uppercase() || c == '_'
}

fn is_digit(c: char) -> bool {
    c.is_ascii_digit()
}

#[cfg(test)]
mod test {
    use core::ascii;
    use log::{error, info};

    use crate::lexer::Lexer;
    use crate::token::TokenKind;

    struct Test {
        pub expected_kind: TokenKind,
        pub expected_literal: String,
    }

    impl Test {
        // literalに渡される文字列がascii文字列であることを仮定している
        fn new(kind: TokenKind, literal: &str) -> Self {
            Self {
                expected_kind: kind,
                expected_literal: literal.to_string(),
            }
        }
    }

    #[test]
    fn read_char() {
        let input = "let five = 5;";
        let mut lexer = Lexer::new(input);

        assert!(lexer.position == 0);
        assert!(lexer.read_position == 1);
        assert!(lexer.peek_char() == 'e');

        lexer.read_char();

        assert!(lexer.position == 1);
        assert!(lexer.read_position == 2);
        assert!(lexer.c == 'e');
        assert!(lexer.peek_char() == 't');
    }

    #[test]
    fn read_identifier() {
        let input = "let five = 5;";
        let mut lexer = Lexer::new(input);

        let ident = lexer.read_identifier();
        if ident.as_str() != "let" {
            panic!("expected: let, got: {}", ident.as_str());
        }

        lexer.skip_whitespace();

        let ident = lexer.read_identifier();
        if ident.as_str() != "five" {
            panic!("expected: five, got: {}", ident.as_str());
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
            [1, 2];
            {\"foo\": \"bar\"}
            ";

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
            Test::new(TokenKind::LeftBracket, "["),
            Test::new(TokenKind::Int, "1"),
            Test::new(TokenKind::Comma, ","),
            Test::new(TokenKind::Int, "2"),
            Test::new(TokenKind::RightBracket, "]"),
            Test::new(TokenKind::Semicolon, ";"),
            Test::new(TokenKind::LeftBrace, "{"),
            Test::new(TokenKind::String, "foo"),
            Test::new(TokenKind::Colon, ":"),
            Test::new(TokenKind::String, "bar"),
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
    fn test_next_token2() {
        let input = "
            let five = 5;
            let ten = 10;

            let add = fn(x, y) {
            x + y;
            };

            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;";

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
            ";

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
            ";

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
