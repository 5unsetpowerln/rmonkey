use std::collections::BTreeMap;
use std::sync::LazyLock;

use anyhow::{Context, Result, anyhow, ensure};
use indexmap::IndexMap;

use crate::ast::{
    ArrayLiteral, BlockStatement, BoolLiteral, CallExpression, Expression, ExpressionStatement,
    FunctionLiteral, HashLiteral, Identifier, IfExpression, IndexExpression, InfixExpression,
    IntegerLiteral, LetStatement, PrefixExpression, Program, ReturnStatement, Statement,
    StringLiteral,
};
use crate::lexer::Lexer;
use crate::token::{Token, TokenKind};

// pratt parsingで使われるトークンに関連付けられる2つの関数のタイプ
// 'aは所有者のライフタイム。所有者自身の可変参照が渡される(すなわちメソッドである)ことを想定している
type PrefixParseFn<'a> = fn(&mut Parser<'a>) -> Result<Expression>;
type InfixParseFn<'a> = fn(&mut Parser<'a>, Expression) -> Result<Expression>;

// 演算の優先順位
#[repr(u16)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum OperationPrecedences {
    Lowest,
    Equals,      // ==
    LessGreater, // > or <
    Sum,         // +
    Product,     // *
    Prefix,      // -X or !X
    Call,        // myFunction(X)
    Index,       // array[x]
}

// 演算子と優先順位の対応
static PRECEDENCES: LazyLock<IndexMap<TokenKind, OperationPrecedences>> = LazyLock::new(|| {
    let mut map = IndexMap::new();

    map.insert(TokenKind::Eq, OperationPrecedences::Equals);
    map.insert(TokenKind::NotEq, OperationPrecedences::Equals);
    map.insert(TokenKind::LessThan, OperationPrecedences::LessGreater);
    map.insert(TokenKind::GreaterThan, OperationPrecedences::LessGreater);
    map.insert(TokenKind::Plus, OperationPrecedences::Sum);
    map.insert(TokenKind::Minus, OperationPrecedences::Sum);
    map.insert(TokenKind::Slash, OperationPrecedences::Product);
    map.insert(TokenKind::Asterisk, OperationPrecedences::Product);
    map.insert(TokenKind::LeftParen, OperationPrecedences::Call);
    map.insert(TokenKind::LeftBracket, OperationPrecedences::Index);

    map
});

// Parser
pub struct Parser<'a> {
    lexer: &'a mut Lexer,
    current_token: Token, // 現在のトークン
    peek_token: Token,    // 一つ先のトークン
    prefix_parse_fns: IndexMap<TokenKind, PrefixParseFn<'a>>,
    infix_parse_fns: IndexMap<TokenKind, InfixParseFn<'a>>,
}
impl<'a> Parser<'a> {
    pub fn empty(lexer: &'a mut Lexer) -> Self {
        Self {
            lexer,
            current_token: Token::empty(),
            peek_token: Token::empty(),
            prefix_parse_fns: IndexMap::new(),
            infix_parse_fns: IndexMap::new(),
        }
    }

    pub fn new(lexer: &'a mut Lexer) -> Self {
        let mut parser = Self::empty(lexer);

        // 2回next_tokenを実行するのでcurrent_tokenとpeek_tokenの両方に値が設定される
        parser.next_token();
        parser.next_token();

        parser.register_prefix(TokenKind::Ident, Self::parse_identifier);
        parser.register_prefix(TokenKind::Int, Self::parse_integer_literal);
        parser.register_prefix(TokenKind::True, Self::parse_bool_literal);
        parser.register_prefix(TokenKind::False, Self::parse_bool_literal);
        parser.register_prefix(TokenKind::LeftParen, Self::parse_grouped_expression);
        parser.register_prefix(TokenKind::If, Self::parse_if_expression);
        parser.register_prefix(TokenKind::Function, Self::parse_function_literal);
        parser.register_prefix(TokenKind::String, Self::parse_string_literal);
        parser.register_prefix(TokenKind::LeftBracket, Self::parse_array_literal);
        parser.register_prefix(TokenKind::LeftBrace, Self::parse_hash_literal);

        parser.register_prefix(TokenKind::Minus, Self::parse_prefix_expression);
        parser.register_prefix(TokenKind::Exclamation, Self::parse_prefix_expression);

        parser.register_infix(TokenKind::LeftParen, Self::parse_call_expression);
        parser.register_infix(TokenKind::LeftBracket, Self::parse_index_expression);

        parser.register_infix(TokenKind::Plus, Self::parse_infix_expression);
        parser.register_infix(TokenKind::Minus, Self::parse_infix_expression);
        parser.register_infix(TokenKind::Slash, Self::parse_infix_expression);
        parser.register_infix(TokenKind::Asterisk, Self::parse_infix_expression);
        parser.register_infix(TokenKind::Eq, Self::parse_infix_expression);
        parser.register_infix(TokenKind::NotEq, Self::parse_infix_expression);
        parser.register_infix(TokenKind::GreaterThan, Self::parse_infix_expression);
        parser.register_infix(TokenKind::LessThan, Self::parse_infix_expression);

        parser
    }

    fn register_prefix(&mut self, token_kind: TokenKind, f: PrefixParseFn<'a>) {
        self.prefix_parse_fns.insert(token_kind, f);
    }

    fn register_infix(&mut self, token_kind: TokenKind, f: InfixParseFn<'a>) {
        self.infix_parse_fns.insert(token_kind, f);
    }

    fn next_token(&mut self) {
        core::mem::swap(&mut self.current_token, &mut self.peek_token);
        self.peek_token = self.lexer.next_token();
    }

    pub fn parse_program(&mut self) -> Result<Program> {
        let mut program = Program::new();

        loop {
            if self.current_token.kind == TokenKind::Eof {
                break;
            }

            let stmt = self
                .parse_statement()
                .context("failed to parse a statement.")?;
            program.statements.push(stmt);

            self.next_token();
        }

        Ok(program)
    }

    fn parse_statement(&mut self) -> Result<Statement> {
        match self.current_token.kind {
            TokenKind::Let => Ok(Statement::Let(self.parse_let_statement()?)),
            TokenKind::Return => Ok(Statement::Return(self.parse_return_statement()?)),
            _ => Ok(Statement::Expression(self.parse_expression_statement()?)),
        }
    }

    fn parse_let_statement(&mut self) -> Result<LetStatement> {
        let token = self.current_token.clone();

        // 次のトークンがIdentifierであることを確認する
        if !self.peek_token_is(TokenKind::Ident) {
            return Err(anyhow!("first token is not identifier."));
        }

        // 次のトークンに進める
        self.next_token();

        // name(Identifier)を取得する
        let name = Identifier::new(self.current_token.clone(), &self.current_token.literal);

        // 次のトークンがAssignであることを確認する
        if !self.peek_token_is(TokenKind::Assign) {
            return Err(anyhow!("second token is not assign."));
        }

        self.next_token();
        self.next_token();

        let value = self
            .parse_expression(OperationPrecedences::Lowest)
            .context("failed to parse expression for value.")?;

        if self.peek_token_is(TokenKind::Semicolon) {
            self.next_token();
        }

        Ok(LetStatement::new(token, name, value))
    }

    fn parse_return_statement(&mut self) -> Result<ReturnStatement> {
        let token = self.current_token.clone();

        self.next_token();

        let value = self
            .parse_expression(OperationPrecedences::Lowest)
            .context("failed to parse expression.")?;

        if self.peek_token_is(TokenKind::Semicolon) {
            self.next_token();
        }

        Ok(ReturnStatement::new(token, value))
    }

    fn parse_expression_statement(&mut self) -> Result<ExpressionStatement> {
        let mut expression_stmt = ExpressionStatement::empty();

        expression_stmt.token = self.current_token.clone();

        expression_stmt.value = self
            .parse_expression(OperationPrecedences::Lowest)
            .context("failed to parse an expression.")?;

        if self.peek_token_is(TokenKind::Semicolon) {
            self.next_token();
        }

        Ok(expression_stmt)
    }

    // parsing function for expressions
    fn parse_expression(&mut self, precedence: OperationPrecedences) -> Result<Expression> {
        let prefix = if let Some(p) = self.prefix_parse_fns.get(&self.current_token.kind) {
            p
        } else {
            return Err(anyhow!(
                "no functions associated to token {:?}",
                self.current_token
            ));
        };

        let mut left_expr = prefix(self).with_context(|| {
            format!(
                "failed to parse {:?} with its associated function.",
                self.current_token
            )
        })?;

        while !self.peek_token_is(TokenKind::Semicolon) && precedence < self.peek_precedence() {
            let infix = if let Some(&infix) = self.infix_parse_fns.get(&self.peek_token.kind) {
                infix
            } else {
                return Ok(left_expr);
            };

            self.next_token();

            left_expr = infix(self, left_expr)?;
        }

        Ok(left_expr)
    }

    fn parse_identifier(&mut self) -> Result<Expression> {
        Ok(Expression::Identifier(Identifier::new(
            self.current_token.clone(),
            &self.current_token.literal,
        )))
    }

    fn parse_integer_literal(&mut self) -> Result<Expression> {
        let value_raw = self.current_token.literal.as_str();
        let value = value_raw
            .parse::<i64>()
            .with_context(|| format!("failed to parse {value_raw} as integer."))?;

        Ok(Expression::IntegerLiteral(IntegerLiteral::new(
            self.current_token.clone(),
            value,
        )))
    }

    fn parse_bool_literal(&mut self) -> Result<Expression> {
        let value_raw = self.current_token.literal.as_str();
        let value = value_raw
            .parse::<bool>()
            .with_context(|| format!("failed to parse {value_raw} as bool."))?;

        Ok(Expression::BoolLiteral(BoolLiteral::new(
            self.current_token.clone(),
            value,
        )))
    }

    fn parse_string_literal(&mut self) -> Result<Expression> {
        Ok(Expression::StringLiteral(StringLiteral::new(
            self.current_token.clone(),
            &self.current_token.literal,
        )))
    }

    fn parse_array_literal(&mut self) -> Result<Expression> {
        let token = self.current_token.clone();

        let expr_list = self
            .parse_expression_list(TokenKind::RightBracket)
            .context("failed to parse expression list.")?;

        Ok(Expression::ArrayLiteral(ArrayLiteral::new(
            token, &expr_list,
        )))
    }

    fn parse_hash_literal(&mut self) -> Result<Expression> {
        let token = self.current_token.clone();

        // {a:b,c:d}
        // ^

        if self.peek_token_is(TokenKind::RightBrace) {
            self.next_token();

            return Ok(Expression::HashLiteral(HashLiteral::new(token, Vec::new())));
        }

        self.next_token();

        // {a:b,c:d}
        //  ^

        let mut map = Vec::new();

        loop {
            let left = self
                .parse_expression(OperationPrecedences::Lowest)
                .context("failed to parse an expression in the hash.")?;

            ensure!(
                self.peek_token_is(TokenKind::Colon),
                "pair expressions are not separated by comma. got: {:?}",
                self.peek_token
            );

            self.next_token();
            self.next_token();

            let right = self
                .parse_expression(OperationPrecedences::Lowest)
                .context("failed to parse an expression in the hash.")?;

            map.push((left, right));

            if !self.peek_token_is(TokenKind::Comma) {
                break;
            }

            self.next_token();
            self.next_token();
        }

        ensure!(
            self.peek_token_is(TokenKind::RightBrace),
            "hash is not closed by \"}}\""
        );

        self.next_token();

        Ok(Expression::HashLiteral(HashLiteral::new(token, map)))
    }

    fn parse_grouped_expression(&mut self) -> Result<Expression> {
        self.next_token();

        let expr = self
            .parse_expression(OperationPrecedences::Lowest)
            .context("failed to parse inner expression.")?;

        ensure!(
            self.peek_token_is(TokenKind::RightParen),
            "grouped expression is not closed.",
        );

        self.next_token();

        Ok(expr)
    }

    fn parse_if_expression(&mut self) -> Result<Expression> {
        let token = self.current_token.clone();

        ensure!(
            self.peek_token_is(TokenKind::LeftParen),
            format!(
                "condition for if expression must be start with '('. got: {:?}",
                self.peek_token
            )
        );

        self.next_token();
        self.next_token();

        let condition = self
            .parse_expression(OperationPrecedences::Lowest)
            .context("failed to parse expression of condition.")?;

        ensure!(
            self.peek_token_is(TokenKind::RightParen),
            format!(
                "condition for if expressoin must be end with ')'. got: {:?}",
                self.peek_token
            )
        );

        self.next_token();

        ensure!(
            self.peek_token_is(TokenKind::LeftBrace),
            format!(
                "consequence for if expressoin must be start with '{{'. got: {:?}",
                self.peek_token
            )
        );

        self.next_token();

        let conseq = self
            .parse_block_statement()
            .context("failed to parse consequence.")?;

        let alternative = if self.peek_token_is(TokenKind::Else) {
            self.next_token();

            ensure!(
                self.peek_token_is(TokenKind::LeftBrace),
                format!(
                    "alternative for else must be start with '{{'. got: {:?}",
                    self.peek_token
                )
            );

            self.next_token();

            Some(
                self.parse_block_statement()
                    .context("failed to parse alternative.")?,
            )
        } else {
            None
        };

        Ok(Expression::If(IfExpression::new(
            token,
            condition,
            conseq,
            alternative,
        )))
    }

    fn parse_function_literal(&mut self) -> Result<Expression> {
        let token = self.current_token.clone();

        ensure!(
            self.peek_token_is(TokenKind::LeftParen),
            "function parameters must start with (."
        );

        self.next_token();

        let params = self
            .parse_function_params()
            .context("failed to parse params.")?;

        ensure!(
            self.peek_token_is(TokenKind::LeftBrace),
            "function block must start with {{."
        );

        self.next_token();

        let block = self
            .parse_block_statement()
            .context("failed to parse function block.")?;

        Ok(Expression::Function(FunctionLiteral::new(
            token, &params, block,
        )))
    }

    fn parse_function_params(&mut self) -> Result<Vec<Identifier>> {
        let mut params = Vec::new();

        if self.peek_token_is(TokenKind::RightParen) {
            return Ok(params);
        }

        self.next_token();

        if let Expression::Identifier(ident) = self
            .parse_identifier()
            .context("failed to parse an identifier.")?
        {
            params.push(ident);
        }

        while self.peek_token_is(TokenKind::Comma) {
            self.next_token();
            self.next_token();

            if let Expression::Identifier(ident) = self
                .parse_identifier()
                .context("failed to parse an identifier.")?
            {
                params.push(ident);
            }
        }

        ensure!(
            self.peek_token_is(TokenKind::RightParen),
            "function parameters must end with )."
        );

        self.next_token();

        Ok(params)
    }

    fn parse_call_expression(&mut self, left: Expression) -> Result<Expression> {
        let token = self.current_token.clone();

        let args = self
            .parse_expression_list(TokenKind::RightParen)
            .context("failed to parse arguments.")?;

        Ok(Expression::Call(CallExpression::new(token, left, &args)))
    }

    fn parse_block_statement(&mut self) -> Result<BlockStatement> {
        let mut statements = Vec::new();
        let token = self.current_token.clone();

        self.next_token();

        while !self.current_token_is(TokenKind::RightBrace)
            && !self.current_token_is(TokenKind::Eof)
        {
            let stmt = self
                .parse_statement()
                .context("failed to parse a statement.")?;

            statements.push(stmt);
            self.next_token();
        }

        Ok(BlockStatement::new(token, &statements))
    }

    fn parse_index_expression(&mut self, left: Expression) -> Result<Expression> {
        // identifier[expression]
        //           ^

        let token = self.current_token.clone();

        self.next_token();

        let index = self
            .parse_expression(OperationPrecedences::Lowest)
            .context("failed to parse expression in index operator.")?;

        self.next_token();

        Ok(Expression::IndexExpression(IndexExpression::new(
            token, left, index,
        )))
    }

    fn parse_prefix_expression(&mut self) -> Result<Expression> {
        let token = self.current_token.clone();
        let operator = &self.current_token.clone().literal;

        self.next_token();

        let right = self
            .parse_expression(OperationPrecedences::Prefix)
            .with_context(|| {
                format!(
                    "failed to parse an expression which is operand of {} (prefix expression)",
                    operator.as_str()
                )
            })?;

        Ok(Expression::Prefix(PrefixExpression::new(
            token, operator, right,
        )))
    }

    fn parse_infix_expression(&mut self, left: Expression) -> Result<Expression> {
        let token = self.current_token.clone();
        let operator = self.current_token.literal.clone();

        let precedence = self.current_precedence();
        self.next_token();
        let right = self
            .parse_expression(precedence)
            .context("failed to parse right expression.")?;

        Ok(Expression::Infix(InfixExpression::new(
            token, &operator, left, right,
        )))
    }

    /// - カンマ区切りの式を解析する。
    /// - 最初の式の直前のトークン指した状態で関数が始まり、渡されたpostfixと一致するトークンを指した状態で関数が終了する。
    /// ```
    /// [expr, expr, ..., expr]
    /// ^
    /// []
    /// ^
    /// ```
    fn parse_expression_list(&mut self, postfix: TokenKind) -> Result<Vec<Expression>> {
        let mut expr_list = Vec::new();

        if self.peek_token_is(postfix) {
            return Ok(expr_list);
        }

        self.next_token();

        loop {
            let expr = self
                .parse_expression(OperationPrecedences::Lowest)
                .with_context(|| {
                    format!(
                        "failed to parse expression {} in expression list.",
                        expr_list.len()
                    )
                })?;

            expr_list.push(expr);

            if !self.peek_token_is(TokenKind::Comma) {
                break;
            }

            self.next_token();
            self.next_token();
        }

        ensure!(
            self.peek_token_is(postfix),
            "postfix token of the expression list is wrong. got: {:?}, expected: {:?}",
            self.peek_token.kind,
            postfix
        );

        self.next_token();

        Ok(expr_list)
    }

    // helper functions
    fn current_token_is(&self, kind: TokenKind) -> bool {
        self.current_token.kind == kind
    }

    fn peek_token_is(&self, kind: TokenKind) -> bool {
        self.peek_token.kind == kind
    }

    fn peek_precedence(&self) -> OperationPrecedences {
        *PRECEDENCES
            .get(&self.peek_token.kind)
            .unwrap_or(&OperationPrecedences::Lowest)
    }

    fn current_precedence(&self) -> OperationPrecedences {
        *PRECEDENCES
            .get(&self.current_token.kind)
            .unwrap_or(&OperationPrecedences::Lowest)
    }

    // pub fn print_errors(&self) {
    //     for err in self.errors.iter() {
    //         println!("parse error: {err}");

    //         let mut current = err.source();

    //         while let Some(s) = current {
    //             println!("<- {s}");
    //             current = s.source();
    //         }
    //     }
    // }
}

// #[cfg(test)]
mod test {
    use anyhow::{Context, Result, anyhow, bail, ensure};

    use super::Parser;
    use crate::ast::{Expression, ExpressionStatement, InfixExpression, NodeInterface, Statement};
    use crate::lexer::Lexer;
    use crate::utils::print_errors;
    use core::ascii;

    enum LiteralForTest {
        Int(i64),
        Ident(Vec<ascii::Char>),
        Bool(bool),
    }

    impl LiteralForTest {
        fn int(value: i64) -> Self {
            Self::Int(value)
        }
        fn ident(value: &str) -> Self {
            Self::Ident(value.as_ascii().unwrap().to_vec())
        }

        fn bool(value: bool) -> Self {
            Self::Bool(value)
        }
    }

    fn parse_single_statement(input: &[ascii::Char]) -> Result<Statement> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);

        let program = parser.parse_program().context("failed to parse program")?;

        ensure!(
            program.statements.len() == 1,
            "number of statement of program is not 1. got: {}",
            program.statements.len()
        );

        let stmt = &program.statements[0];

        Ok(stmt.clone())
    }

    fn parse_single_expression_statement(input: &[ascii::Char]) -> Result<ExpressionStatement> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);

        let program = parser.parse_program().context("failed to parse program")?;

        ensure!(
            program.statements.len() == 1,
            "number of statement of program is not 1. got: {}",
            program.statements.len()
        );

        let stmt = &program.statements[0];

        let expr_stmt = if let Statement::Expression(expr_stmt) = stmt {
            expr_stmt
        } else {
            bail!(anyhow!(
                "stmt is not ExpressoinStatement. got: {}",
                stmt.string().as_str()
            ))
        };

        Ok(expr_stmt.clone())
    }

    #[test]
    fn test_let_statements1() {
        struct Test {
            input: Vec<ascii::Char>,
            expected_identifier: Vec<ascii::Char>,
            expected_value: LiteralForTest,
        }
        impl Test {
            fn new(input: &str, expected_identifier: &str, expected_value: LiteralForTest) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    expected_identifier: expected_identifier.as_ascii().unwrap().to_vec(),
                    expected_value,
                }
            }
        }

        let tests = vec![
            Test::new("let x = 5;", "x", LiteralForTest::int(5)),
            Test::new("let y = true;", "y", LiteralForTest::bool(true)),
            Test::new("let foobar = y;", "foobar", LiteralForTest::ident("y")),
        ];

        for test in tests.iter() {
            let stmt = &parse_single_statement(&test.input).unwrap_or_else(|err| {
                print_errors("failed to parse single statement", err);
                panic!();
            });

            test_let_statement(stmt, &test.expected_identifier);

            let let_stmt = if let Statement::Let(let_stmt) = stmt {
                let_stmt
            } else {
                panic!("stmt is not LetStatement. got: {}", stmt.string().as_str());
            };

            test_literal_expression(&let_stmt.value, &test.expected_value);
        }
    }

    fn test_let_statement(stmt: &Statement, name: &[ascii::Char]) {
        if stmt.token_literal().as_str() != "let" {
            panic!(
                "stmt.token_literal not 'let'. got: {}",
                stmt.token_literal().as_str()
            );
        }

        let let_stmt = if let Statement::Let(let_stmt) = stmt {
            let_stmt
        } else {
            panic!("stmt not let statement. got: {stmt:?}");
        };

        if let_stmt.name.value != name {
            panic!(
                "let_stmt.name.value is not {}. got: {}",
                name.as_str(),
                let_stmt.name.value.as_str()
            )
        }

        if let_stmt.name.token_literal() != name {
            panic!(
                "let_stmt.name.token_literal() is not {}. got: {}",
                name.as_str(),
                let_stmt.name.token_literal().as_str(),
            );
        }
    }

    #[test]
    fn test_return_statements1() {
        struct Test {
            input: Vec<ascii::Char>,
            expected_value: LiteralForTest,
        }
        impl Test {
            fn new(input: &str, expected_value: LiteralForTest) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    expected_value,
                }
            }
        }

        let tests = vec![
            Test::new("return 5;", LiteralForTest::int(5)),
            Test::new("return true;", LiteralForTest::bool(true)),
            Test::new("return foobar;", LiteralForTest::ident("foobar")),
        ];

        for test in tests.iter() {
            let stmt = &parse_single_statement(&test.input).unwrap_or_else(|err| {
                print_errors("failed to parse single statement", err);
                panic!();
            });

            let ret_stmt = if let Statement::Return(ret_stmt) = stmt {
                ret_stmt
            } else {
                panic!(
                    "stmt is not ReturnStatement. got: {}",
                    stmt.string().as_str()
                );
            };

            if ret_stmt.token_literal().as_str() != "return" {
                panic!(
                    "ret_stmt.token_literal() is not 'return'. got: {}",
                    ret_stmt.token_literal().as_str()
                );
            }

            test_literal_expression(&ret_stmt.value, &test.expected_value);
        }
    }

    #[test]
    fn test_identifier_expression() {
        let input = "foobar;".as_ascii().unwrap();

        let expr_stmt = parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse single expression statement", err);
            panic!()
        });

        let ident = if let Expression::Identifier(ident) = &expr_stmt.value {
            ident
        } else {
            panic!("Expression is not Identifier. got: {:?}", expr_stmt.value);
        };

        if ident.value != "foobar".as_ascii().unwrap() {
            panic!(
                "ident.value is not \"foobar\". got: {}",
                ident.value.as_str()
            );
        }

        if ident.token_literal() != "foobar".as_ascii().unwrap() {
            panic!(
                "ident.token_literal() is not \"foobar\". got: {}",
                ident.token_literal().as_str()
            );
        }
    }

    #[test]
    fn test_integer_literal_expression() {
        let input = "5".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let literal = if let Expression::IntegerLiteral(literal) = &expr_stmt.value {
            literal
        } else {
            panic!("expr is not IntegerLiteral. got: {:?}", &expr_stmt.value);
        };

        if literal.value != 5 {
            panic!("literal.value is not 5. got: {}", &literal.value);
        }

        if literal.token_literal() != "5".as_ascii().unwrap() {
            panic!(
                "literal.token_literal() is not \"5\". got: {}",
                literal.token_literal().as_str()
            );
        }
    }

    #[test]
    fn test_parsing_prefix_expression1() {
        struct Test {
            input: Vec<ascii::Char>,
            operator: Vec<ascii::Char>,
            value: LiteralForTest,
        }
        impl Test {
            fn new(input: &str, operator: &str, value: LiteralForTest) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    operator: operator.as_ascii().unwrap().to_vec(),
                    value,
                }
            }
        }

        let tests = vec![
            Test::new("!5;", "!", LiteralForTest::int(5)),
            Test::new("-15;", "-", LiteralForTest::int(15)),
            Test::new("!foobar;", "!", LiteralForTest::ident("foobar")),
            Test::new("-foobar;", "-", LiteralForTest::ident("foobar")),
            Test::new("!true", "!", LiteralForTest::bool(true)),
            Test::new("!false", "!", LiteralForTest::bool(false)),
        ];

        for test in tests.iter() {
            let expr_stmt = &parse_single_expression_statement(&test.input).unwrap_or_else(|err| {
                print_errors("failed to parse expression statement", err);
                panic!();
            });

            let prefix_expr = if let Expression::Prefix(prefix_expr) = &expr_stmt.value {
                prefix_expr
            } else {
                panic!(
                    "expr_stmt.value is not PrefixExpression. got: {:?}",
                    &expr_stmt.value
                );
            };

            if prefix_expr.operator != test.operator {
                panic!(
                    "expr.operator is not {}. got: {}",
                    test.operator.as_str(),
                    prefix_expr.operator.as_str()
                );
            }

            test_literal_expression(&prefix_expr.right, &test.value);
        }
    }

    #[test]
    fn test_parsing_infix_expressions1() {
        struct Test {
            input: Vec<ascii::Char>,
            left: LiteralForTest,
            operator: Vec<ascii::Char>,
            right: LiteralForTest,
        }
        impl Test {
            fn new(
                input: &str,
                left: LiteralForTest,
                operator: &str,
                right: LiteralForTest,
            ) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    operator: operator.as_ascii().unwrap().to_vec(),
                    left,
                    right,
                }
            }
        }

        let tests = vec![
            Test::new(
                "5 + 5;",
                LiteralForTest::int(5),
                "+",
                LiteralForTest::int(5),
            ),
            Test::new(
                "5 - 5;",
                LiteralForTest::int(5),
                "-",
                LiteralForTest::int(5),
            ),
            Test::new(
                "5 * 5;",
                LiteralForTest::int(5),
                "*",
                LiteralForTest::int(5),
            ),
            Test::new(
                "5 / 5;",
                LiteralForTest::int(5),
                "/",
                LiteralForTest::int(5),
            ),
            Test::new(
                "5 > 5;",
                LiteralForTest::int(5),
                ">",
                LiteralForTest::int(5),
            ),
            Test::new(
                "5 < 5;",
                LiteralForTest::int(5),
                "<",
                LiteralForTest::int(5),
            ),
            Test::new(
                "5 == 5;",
                LiteralForTest::int(5),
                "==",
                LiteralForTest::int(5),
            ),
            Test::new(
                "5 != 5;",
                LiteralForTest::int(5),
                "!=",
                LiteralForTest::int(5),
            ),
            Test::new(
                "foobar + barfoo;",
                LiteralForTest::ident("foobar"),
                "+",
                LiteralForTest::ident("barfoo"),
            ),
            Test::new(
                "foobar - barfoo;",
                LiteralForTest::ident("foobar"),
                "-",
                LiteralForTest::ident("barfoo"),
            ),
            Test::new(
                "foobar * barfoo;",
                LiteralForTest::ident("foobar"),
                "*",
                LiteralForTest::ident("barfoo"),
            ),
            Test::new(
                "foobar / barfoo;",
                LiteralForTest::ident("foobar"),
                "/",
                LiteralForTest::ident("barfoo"),
            ),
            Test::new(
                "foobar > barfoo;",
                LiteralForTest::ident("foobar"),
                ">",
                LiteralForTest::ident("barfoo"),
            ),
            Test::new(
                "foobar < barfoo;",
                LiteralForTest::ident("foobar"),
                "<",
                LiteralForTest::ident("barfoo"),
            ),
            Test::new(
                "foobar == barfoo;",
                LiteralForTest::ident("foobar"),
                "==",
                LiteralForTest::ident("barfoo"),
            ),
            Test::new(
                "foobar != barfoo;",
                LiteralForTest::ident("foobar"),
                "!=",
                LiteralForTest::ident("barfoo"),
            ),
            Test::new(
                "true == true",
                LiteralForTest::bool(true),
                "==",
                LiteralForTest::bool(true),
            ),
            Test::new(
                "true != false",
                LiteralForTest::bool(true),
                "!=",
                LiteralForTest::bool(false),
            ),
            Test::new(
                "false == false",
                LiteralForTest::bool(false),
                "==",
                LiteralForTest::bool(false),
            ),
        ];

        for test in tests.iter() {
            let expr_stmt = &parse_single_expression_statement(&test.input).unwrap_or_else(|err| {
                print_errors("failed to parse expression statement", err);
                panic!();
            });

            test_infix_expression(&expr_stmt.value, &test.left, &test.operator, &test.right);
        }
    }

    #[test]
    fn test_operator_precedence_parsing() {
        struct Test {
            input: Vec<ascii::Char>,
            expected: Vec<ascii::Char>,
        }
        impl Test {
            fn new(input: &str, expected: &str) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    expected: expected.as_ascii().unwrap().to_vec(),
                }
            }
        }

        let tests = vec![
            Test::new("-a * b", "((-a) * b)"),
            Test::new("!-a", "(!(-a))"),
            Test::new("a + b + c", "((a + b) + c)"),
            Test::new("a + b - c", "((a + b) - c)"),
            Test::new("a * b * c", "((a * b) * c)"),
            Test::new("a * b / c", "((a * b) / c)"),
            Test::new("a + b / c", "(a + (b / c))"),
            Test::new("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            Test::new("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
            Test::new("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            Test::new("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            Test::new(
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            Test::new("true", "true"),
            Test::new("false", "false"),
            Test::new("3 > 5 == false", "((3 > 5) == false)"),
            Test::new("3 < 5 == true", "((3 < 5) == true)"),
            Test::new("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            Test::new("(5 + 5) * 2", "((5 + 5) * 2)"),
            Test::new("2 / (5 + 5)", "(2 / (5 + 5))"),
            Test::new("(5 + 5) * 2 * (5 + 5)", "(((5 + 5) * 2) * (5 + 5))"),
            Test::new("-(5 + 5)", "(-(5 + 5))"),
            Test::new("!(true == true)", "(!(true == true))"),
            Test::new("a + add(b * c) + d", "((a + add((b * c))) + d)"),
            Test::new(
                "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            ),
            Test::new(
                "add(a + b + c * d / f + g)",
                "add((((a + b) + ((c * d) / f)) + g))",
            ),
            Test::new(
                "a * [1, 2, 3, 4][b * c] * d",
                "((a * ([1, 2, 3, 4][(b * c)])) * d)",
            ),
            Test::new(
                "add(a * b[2], b[1], 2 * [1, 2][1])",
                "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))",
            ),
            Test::new(
                "a * [1, 2, 3, 4][b * c] * d",
                "((a * ([1, 2, 3, 4][(b * c)])) * d)",
            ),
            Test::new(
                "add(a * b[2], b[1], 2 * [1, 2][1])",
                "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))",
            ),
        ];

        for test in tests.iter() {
            let mut lexer = Lexer::new(&test.input);
            let mut parser = Parser::new(&mut lexer);

            let program = match parser.parse_program() {
                Ok(p) => p,
                Err(err) => {
                    print_errors("failed to parse the program", err);
                    panic!()
                }
            };

            let actual = program.string();
            if actual != test.expected {
                panic!(
                    "expected: {}, got: {}",
                    test.expected.as_str(),
                    actual.as_str()
                );
            }
        }
    }

    #[test]
    fn test_boolean_expression() {
        struct Test {
            input: Vec<ascii::Char>,
            expected_boolean: bool,
        }
        impl Test {
            fn new(input: &str, expected_boolean: bool) -> Self {
                Self {
                    input: input.as_ascii().unwrap().to_vec(),
                    expected_boolean,
                }
            }
        }

        let tests = vec![Test::new("true;", true), Test::new("false;", false)];

        for test in tests.iter() {
            let expr_stmt = &parse_single_expression_statement(&test.input).unwrap_or_else(|err| {
                print_errors("failed to parse expression statement", err);
                panic!();
            });

            let bool_expr = if let Expression::BoolLiteral(bool_expr) = &expr_stmt.value {
                bool_expr
            } else {
                panic!(
                    "expr_stmt.value is not Boolean. got: {}",
                    expr_stmt.value.string().as_str()
                );
            };

            if bool_expr.value != test.expected_boolean {
                panic!(
                    "bool_expr.value is not {}. got: {}",
                    test.expected_boolean, bool_expr.value
                );
            }
        }
    }

    #[test]
    fn test_if_expression() {
        let input = "if (x < y) {x}".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let if_expr = if let Expression::If(if_expr) = &expr_stmt.value {
            if_expr
        } else {
            panic!(
                "expr_stmt.value is not IfExpression. got: {}",
                expr_stmt.value.string().as_str()
            );
        };

        test_infix_expression(
            &if_expr.condition,
            &LiteralForTest::ident("x"),
            "<".as_ascii().unwrap(),
            &LiteralForTest::ident("y"),
        );

        if if_expr.consequence.statements.len() != 1 {
            panic!(
                "consequence is not 1 statement. got: {}",
                if_expr.consequence.statements.len()
            );
        }

        let expr_stmt_in_conseq =
            if let Statement::Expression(expr_stmt) = &if_expr.consequence.statements[0] {
                expr_stmt
            } else {
                panic!(
                    "if_expr.consequence.statements[0] is not ExpressionStatement. got: {:?}",
                    &if_expr.consequence.statements[0]
                );
            };

        test_identifier(&expr_stmt_in_conseq.value, "x".as_ascii().unwrap());

        if if_expr.alternative.is_some() {
            panic!("if_expr.alternative is not None.");
        }
    }

    #[test]
    fn test_if_else_expression() {
        let input = "if (x < y) {x} else {y}".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let if_expr = if let Expression::If(if_expr) = &expr_stmt.value {
            if_expr
        } else {
            panic!(
                "expr_stmt.value is not IfExpression. got: {}",
                expr_stmt.value.string().as_str()
            );
        };

        test_infix_expression(
            &if_expr.condition,
            &LiteralForTest::ident("x"),
            "<".as_ascii().unwrap(),
            &LiteralForTest::ident("y"),
        );

        if if_expr.consequence.statements.len() != 1 {
            panic!(
                "consequence is not 1 statement. got: {}",
                if_expr.consequence.statements.len()
            );
        }

        let expr_stmt_in_conseq =
            if let Statement::Expression(expr_stmt) = &if_expr.consequence.statements[0] {
                expr_stmt
            } else {
                panic!(
                    "if_expr.consequence.statements[0] is not ExpressionStatement. got: {:?}",
                    &if_expr.consequence.statements[0]
                );
            };

        test_identifier(&expr_stmt_in_conseq.value, "x".as_ascii().unwrap());

        let alternative = if let Some(a) = &if_expr.alternative {
            a
        } else {
            panic!("if_expr.alternative is None.");
        };

        if alternative.statements.len() != 1 {
            panic!(
                "expr_stmt.alternative.statements is not 1 statement. got: {}",
                alternative.statements.len()
            );
        }

        let expr_stmt_in_alt = if let Statement::Expression(expr_stmt) = &alternative.statements[0]
        {
            expr_stmt
        } else {
            panic!(
                "if_expr.alternative.statements[0] is not ExpressionStatement. got: {:?}",
                &alternative.statements[0]
            );
        };

        test_identifier(&expr_stmt_in_alt.value, "y".as_ascii().unwrap());
    }

    #[test]
    fn test_function_literal_parsing() {
        let input = "fn(x, y) { x + y; }".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let func_literal = if let Expression::Function(func_literal) = &expr_stmt.value {
            func_literal
        } else {
            panic!(
                "expr_stmt.value is not FunctionLiteral. got: {:?}",
                expr_stmt.value
            );
        };

        if func_literal.params.len() != 2 {
            panic!(
                "func_literal.parameters is not 2 parameters. got: {}",
                func_literal.params.len()
            );
        }

        test_literal_expression(
            &Expression::Identifier(func_literal.params[0].clone()),
            &LiteralForTest::ident("x"),
        );

        test_literal_expression(
            &Expression::Identifier(func_literal.params[1].clone()),
            &LiteralForTest::ident("y"),
        );

        if func_literal.body.statements.len() != 1 {
            panic!(
                "func_literal.body.statements is not 1 statement. got: {}",
                func_literal.body.statements.len()
            );
        }

        let body_stmt = if let Statement::Expression(s) = &func_literal.body.statements[0] {
            s
        } else {
            panic!("func_literal.body.statements[0] is not ExpressionStatement");
        };

        let body_expr = &body_stmt.value;
        test_infix_expression(
            body_expr,
            &LiteralForTest::ident("x"),
            "+".as_ascii().unwrap(),
            &LiteralForTest::ident("y"),
        );
    }

    #[test]
    fn test_string_literal_expression() {
        let input = "\"hello world\";".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let string_literal = if let Expression::StringLiteral(s) = &expr_stmt.value {
            s
        } else {
            panic!(
                "expr_stmt.value is not StringLiteral. got: {:?}",
                &expr_stmt.value
            );
        };

        if string_literal.value.as_str() != "hello world" {
            panic!(
                "string_literal.value is not \"hello world\". got: {}",
                string_literal.value.as_str()
            );
        }
    }

    #[test]
    fn test_call_expression_parsing() {
        let input = "add(1, 2 * 3, 4 + 5);".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let call_expr = if let Expression::Call(call_expr) = &expr_stmt.value {
            call_expr
        } else {
            panic!("expr_stmt.value is not CallExpression");
        };

        test_identifier(&call_expr.func, "add".as_ascii().unwrap());

        if call_expr.args.len() != 3 {
            panic!("wrong length of args. got: {}", call_expr.args.len());
        }

        test_literal_expression(&call_expr.args[0], &LiteralForTest::int(1));
        test_infix_expression(
            &call_expr.args[1],
            &LiteralForTest::int(2),
            "*".as_ascii().unwrap(),
            &LiteralForTest::int(3),
        );
        test_infix_expression(
            &call_expr.args[2],
            &LiteralForTest::int(4),
            "+".as_ascii().unwrap(),
            &LiteralForTest::int(5),
        );
    }

    #[test]
    fn test_parsing_array_literals() {
        let input = "[1, 2 * 2, 3 + 3]".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let array_literal = if let Expression::ArrayLiteral(array_literal) = &expr_stmt.value {
            array_literal
        } else {
            panic!("expr_stmt.value is not ArrayLiteral");
        };

        if array_literal.elements.len() != 3 {
            panic!(
                "array_literal.elements.len() is not 3. got: {}",
                array_literal.elements.len()
            );
        }

        test_integer_literal(&array_literal.elements[0], 1);
        test_infix_expression(
            &array_literal.elements[1],
            &LiteralForTest::int(2),
            "*".as_ascii().unwrap(),
            &LiteralForTest::int(2),
        );
        test_infix_expression(
            &array_literal.elements[2],
            &LiteralForTest::int(3),
            "+".as_ascii().unwrap(),
            &LiteralForTest::int(3),
        );
    }

    #[test]
    fn test_parsing_index_expressions() {
        let input = "myArray[1 + 1]".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let idx_expr = if let Expression::IndexExpression(idx_expr) = &expr_stmt.value {
            idx_expr
        } else {
            panic!("expr_stmt.value is not IndexExpression");
        };

        test_identifier(&idx_expr.left, "myArray".as_ascii().unwrap());

        test_infix_expression(
            &idx_expr.index,
            &LiteralForTest::int(1),
            "+".as_ascii().unwrap(),
            &LiteralForTest::int(1),
        );
    }

    #[test]
    fn test_parsing_hash_literals_string_keys() {
        let input = "{\"one\": 1, \"two\": 2, \"three\": 3}".as_ascii().unwrap();
        let expected = vec![("one", 1), ("two", 2), ("three", 3)];

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let hash_literal = if let Expression::HashLiteral(hash_literal) = &expr_stmt.value {
            hash_literal
        } else {
            panic!("expr_stmt.value is not HashLiteral");
        };

        if hash_literal.pairs.0.len() != 3 {
            panic!(
                "hash_literal.pairs has wrong length. got: {}, expected: {}",
                hash_literal.pairs.0.len(),
                3
            );
        }

        for (i, (key, value)) in hash_literal.pairs.0.iter().enumerate() {
            println!("{key:?}, {:?}", expected[i]);

            test_string_literal(key, expected[i].0).unwrap_or_else(|err| {
                print_errors(format!("test {i} failed").as_str(), err);
            });
            test_integer_literal(value, expected[i].1);
        }
    }

    #[test]
    fn test_parsing_empty_hash_literal() {
        let input = "{}".as_ascii().unwrap();

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let hash_literal = if let Expression::HashLiteral(hash_literal) = &expr_stmt.value {
            hash_literal
        } else {
            panic!("expr_stmt.value is not HashLiteral");
        };

        if hash_literal.pairs.0.len() != 0 {
            panic!(
                "hash_literal.pairs has wrong length. got: {}, expected: {}",
                hash_literal.pairs.0.len(),
                0
            );
        }
    }

    #[test]
    fn test_parsing_hash_literals_with_expressions() {
        let input = "{\"one\": 0 + 1, \"two\": 10 - 8, \"three\": 15 / 5}"
            .as_ascii()
            .unwrap();

        let expected: Vec<(&str, fn(&Expression))> = vec![
            ("one", |expr: &Expression| {
                test_infix_expression(
                    expr,
                    &LiteralForTest::int(0),
                    "+".as_ascii().unwrap(),
                    &LiteralForTest::int(1),
                );
            }),
            ("two", |expr: &Expression| {
                test_infix_expression(
                    expr,
                    &LiteralForTest::int(10),
                    "-".as_ascii().unwrap(),
                    &LiteralForTest::int(8),
                );
            }),
            ("three", |expr: &Expression| {
                test_infix_expression(
                    expr,
                    &LiteralForTest::int(15),
                    "/".as_ascii().unwrap(),
                    &LiteralForTest::int(5),
                );
            }),
        ];

        let expr_stmt = &parse_single_expression_statement(input).unwrap_or_else(|err| {
            print_errors("failed to parse expression statement", err);
            panic!();
        });

        let hash_literal = if let Expression::HashLiteral(hash_literal) = &expr_stmt.value {
            hash_literal
        } else {
            panic!("expr_stmt.value is not HashLiteral");
        };

        if hash_literal.pairs.0.len() != 3 {
            panic!(
                "hash_literal.pairs has wrong length. got: {}, expected: {}",
                hash_literal.pairs.0.len(),
                3
            );
        }

        for (i, (key, value)) in hash_literal.pairs.0.iter().enumerate() {
            test_string_literal(key, expected[i].0).unwrap_or_else(|err| {
                print_errors(format!("test {i} failed").as_str(), err);
                panic!();
            });
            (expected[i].1)(value);
        }
    }

    fn test_infix_expression(
        expr: &Expression,
        left: &LiteralForTest,
        operator: &[ascii::Char],
        right: &LiteralForTest,
    ) {
        let infix_expr = if let Expression::Infix(infix_expr) = expr {
            infix_expr
        } else {
            panic!("expr is not InfixExpression. got: {expr:?}");
        };

        test_literal_expression(&infix_expr.left, left);

        if infix_expr.operator != operator {
            panic!(
                "infix_expr.operator is not {}. got: {}",
                operator.as_str(),
                infix_expr.operator.as_str()
            );
        }

        test_literal_expression(&infix_expr.right, right);
    }

    fn test_literal_expression(expr: &Expression, expected: &LiteralForTest) {
        match expected {
            LiteralForTest::Int(value) => test_integer_literal(expr, *value),
            LiteralForTest::Ident(value) => test_identifier(expr, value),
            LiteralForTest::Bool(value) => test_boolean_literal(expr, *value),
        }
    }

    fn test_string_literal(expr: &Expression, value: &str) -> Result<()> {
        let string_literal = if let Expression::StringLiteral(sl) = expr {
            sl
        } else {
            bail!(anyhow!("expr is not StringLiteral"));
        };

        ensure!(
            string_literal.value.as_str() == value,
            "string_literal.value is not {}. got: {}",
            value,
            string_literal.value.as_str()
        );

        Ok(())
    }

    fn test_integer_literal(expr: &Expression, value: i64) {
        let integer_literal = if let Expression::IntegerLiteral(il) = expr {
            il
        } else {
            panic!("expr is not IntegerLiteral")
        };

        if integer_literal.value != value {
            panic!(
                "integer_literal.value is not {}. got: {}",
                value, integer_literal.value
            );
        }

        if integer_literal.token_literal().as_str() != format!("{value}").as_str() {
            panic!(
                "integer_literal.token_literal() is not \"{}\". got: \"{}\"",
                value,
                integer_literal.token_literal().as_str()
            );
        }
    }

    fn test_boolean_literal(expr: &Expression, value: bool) {
        let bool_expr = if let Expression::BoolLiteral(bool_expr) = expr {
            bool_expr
        } else {
            panic!("expr is not Boolean. got: {}", expr.string().as_str());
        };

        if bool_expr.value != value {
            panic!("bool_expr.value is not {}. got: {}", value, bool_expr.value);
        }

        if bool_expr.token_literal().as_str() != value.to_string().as_str() {
            panic!(
                "bool_expr.token_literal() is not {}. got: {}",
                value,
                bool_expr.token_literal().as_str()
            );
        }
    }

    // 与えた式が識別子であること、
    // その識別子が与えた文字列と等しいこと、
    // その識別子のトークンリテラルが与えた文字列と等しいことをテストする
    // テストに成功したらリターンし、失敗したらpanicする
    fn test_identifier(expr: &Expression, value: &[ascii::Char]) {
        let ident = if let Expression::Identifier(ident) = expr {
            ident
        } else {
            panic!("expr is not Identifier. got: {expr:?}");
        };

        if ident.value != value {
            panic!(
                "ident value is not {}. got: {}",
                value.as_str(),
                ident.value.as_str()
            );
        }

        if ident.token_literal() != value {
            panic!(
                "ident.token_literal() is not {}. got: {}",
                value.as_str(),
                ident.token_literal().as_str()
            );
        }
    }
}
