use core::ascii;

use crate::token::Token;

// Node
pub enum Node<'a> {
    Expression(&'a Expression),
    Identifier(&'a Identifier),
    IntegerLiteral(&'a IntegerLiteral),
    BoolLiteral(&'a BoolLiteral),
    PrefixExpression(&'a PrefixExpression),
    InfixExpression(&'a InfixExpression),
    IfExpression(&'a IfExpression),
    FunctionLiteral(&'a FunctionLiteral),
    CallExpression(&'a CallExpression),
    BlockStatement(&'a BlockStatement),
    Statement(&'a Statement),
    LetStatement(&'a LetStatement),
    ReturnStatement(&'a ReturnStatement),
    ExpressionStatement(&'a ExpressionStatement),
    Program(&'a Program),
    StringLiteral(&'a StringLiteral),
}

pub trait NodeInterface {
    /// 実体がenumのNode、すなわちExpressionやStatementは、Node::Expression/Statementを返すのではなくて、ラップされているNodeを返す。
    /// 例えば、Expression(IntegerLiteral)に対してget_nodeを呼ぶと、Node::IntegerLiteralが返される。
    fn get_node(&self) -> Node;
    fn token_literal(&self) -> Vec<ascii::Char>;
    fn string(&self) -> Vec<ascii::Char>;
}

// Expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
    Identifier(Identifier),
    IntegerLiteral(IntegerLiteral),
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    BoolLiteral(BoolLiteral),
    If(IfExpression),
    Function(FunctionLiteral),
    Call(CallExpression),
    StringLiteral(StringLiteral),
}

impl Expression {
    pub fn empty() -> Self {
        Self::Identifier(Identifier::empty())
    }

    fn as_node_interface(&self) -> &dyn NodeInterface {
        match self {
            Self::Identifier(x) => x,
            Self::IntegerLiteral(x) => x,
            Self::BoolLiteral(x) => x,
            Self::Call(x) => x,
            Self::Function(x) => x,
            Self::If(x) => x,
            Self::Infix(x) => x,
            Self::Prefix(x) => x,
            Self::StringLiteral(x) => x,
        }
    }
}

impl NodeInterface for Expression {
    fn get_node(&self) -> Node {
        Node::Expression(self)
    }

    fn token_literal(&self) -> Vec<ascii::Char> {
        self.as_node_interface().token_literal()
    }

    fn string(&self) -> Vec<ascii::Char> {
        self.as_node_interface().string()
    }
}

// Identifier
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Identifier {
    pub token: Token,
    pub value: Vec<ascii::Char>,
}
impl Identifier {
    pub fn new(token: Token, value: &[ascii::Char]) -> Self {
        Self {
            token,
            value: value.to_vec(),
        }
    }

    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            value: Vec::new(),
        }
    }
}

impl NodeInterface for Identifier {
    fn get_node(&self) -> Node {
        Node::Identifier(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        self.token_literal()
    }
}

// IntegerLiteral
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerLiteral {
    pub token: Token,
    pub value: i64,
}

impl IntegerLiteral {
    pub fn new(token: Token, value: i64) -> Self {
        Self { token, value }
    }
}

impl NodeInterface for IntegerLiteral {
    fn get_node(&self) -> Node {
        Node::IntegerLiteral(self)
    }

    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        self.token_literal()
    }
}

// Boolean
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolLiteral {
    pub token: Token,
    pub value: bool,
}

impl BoolLiteral {
    pub fn new(token: Token, value: bool) -> Self {
        Self { token, value }
    }
}

impl NodeInterface for BoolLiteral {
    fn get_node(&self) -> Node {
        Node::BoolLiteral(self)
    }

    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }
    fn string(&self) -> Vec<ascii::Char> {
        self.token_literal()
    }
}

// StringLiteral
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringLiteral {
    pub token: Token,
    pub value: Vec<ascii::Char>,
}

impl StringLiteral {
    pub fn new(token: Token, value: &[ascii::Char]) -> Self {
        Self {
            token,
            value: value.to_vec(),
        }
    }
}

impl NodeInterface for StringLiteral {
    fn get_node(&self) -> Node {
        Node::StringLiteral(self)
    }

    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();
        buffer.push(ascii::Char::QuotationMark);
        buffer.extend(&self.value);
        buffer.push(ascii::Char::QuotationMark);
        buffer
    }
}

// PrefixExpression
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrefixExpression {
    pub token: Token,
    pub operator: Vec<ascii::Char>,
    pub right: Box<Expression>,
}

impl PrefixExpression {
    pub fn new(token: Token, operator: &[ascii::Char], right: Expression) -> Self {
        Self {
            token,
            operator: operator.to_vec(),
            right: Box::new(right),
        }
    }

    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            operator: Vec::new(),
            right: Box::new(Expression::empty()),
        }
    }
}

impl NodeInterface for PrefixExpression {
    fn get_node(&self) -> Node {
        Node::PrefixExpression(self)
    }

    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }
    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();

        buffer.push('('.as_ascii().unwrap());
        buffer.extend(&self.operator);
        buffer.extend(&self.right.string());
        buffer.push(')'.as_ascii().unwrap());

        buffer
    }
}

// InfixExpression
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InfixExpression {
    pub token: Token,
    pub operator: Vec<ascii::Char>,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

impl InfixExpression {
    pub fn new(
        token: Token,
        operator: &[ascii::Char],
        left: Expression,
        right: Expression,
    ) -> Self {
        Self {
            token,
            operator: operator.to_vec(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl NodeInterface for InfixExpression {
    fn get_node(&self) -> Node {
        Node::InfixExpression(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();

        buffer.push('('.as_ascii().unwrap());
        buffer.extend(self.left.string());
        buffer.push(' '.as_ascii().unwrap());
        buffer.extend(&self.operator);
        buffer.push(' '.as_ascii().unwrap());
        buffer.extend(self.right.string());
        buffer.push(')'.as_ascii().unwrap());

        buffer
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Box<Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl IfExpression {
    pub fn new(
        token: Token,
        condition: Expression,
        consequence: BlockStatement,
        alternative: Option<BlockStatement>,
    ) -> Self {
        Self {
            token,
            condition: Box::new(condition),
            consequence,
            alternative,
        }
    }
}

impl NodeInterface for IfExpression {
    fn get_node(&self) -> Node {
        Node::IfExpression(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();

        buffer.extend("if".as_ascii().unwrap());
        buffer.extend(self.condition.string());
        buffer.push(' '.as_ascii().unwrap());
        buffer.extend(self.consequence.string());

        if let Some(alternative) = &self.alternative {
            buffer.extend("else ".as_ascii().unwrap());
            buffer.extend(alternative.string());
        }

        buffer
    }
}

// FunctionLiteral
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionLiteral {
    pub token: Token,
    pub params: Vec<Identifier>,
    pub body: BlockStatement,
}

impl FunctionLiteral {
    pub fn new(token: Token, params: &[Identifier], body: BlockStatement) -> Self {
        Self {
            token,
            params: params.to_vec(),
            body,
        }
    }
}

impl NodeInterface for FunctionLiteral {
    fn get_node(&self) -> Node {
        Node::FunctionLiteral(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();

        buffer.extend(self.token_literal());
        buffer.push('('.as_ascii().unwrap());
        for (i, param) in self.params.iter().enumerate() {
            if i != self.params.len() - 1 {
                buffer.extend(param.string());
                buffer.push(','.as_ascii().unwrap());
            }
        }
        buffer.push(')'.as_ascii().unwrap());
        buffer.extend(self.body.string());

        buffer
    }
}

// CallExpression
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallExpression {
    pub token: Token,
    pub func: Box<Expression>,
    pub args: Vec<Expression>,
}

impl CallExpression {
    pub fn new(token: Token, func: Expression, args: &[Expression]) -> Self {
        Self {
            token,
            func: Box::new(func),
            args: args.to_vec(),
        }
    }
}

impl NodeInterface for CallExpression {
    fn get_node(&self) -> Node {
        Node::CallExpression(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();

        buffer.extend(self.func.string());
        buffer.push('('.as_ascii().unwrap());
        for (i, arg) in self.args.iter().enumerate() {
            buffer.extend(arg.string());

            if i != self.args.len() - 1 {
                buffer.extend(", ".as_ascii().unwrap());
            }
        }
        buffer.push(')'.as_ascii().unwrap());

        buffer
    }
}

// BlockStatement
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockStatement {
    pub token: Token, // {
    pub statements: Vec<Statement>,
}

impl BlockStatement {
    pub fn new(token: Token, statements: &[Statement]) -> Self {
        Self {
            token,
            statements: statements.to_vec(),
        }
    }
}

impl NodeInterface for BlockStatement {
    fn get_node(&self) -> Node {
        Node::BlockStatement(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();
        for stmt in self.statements.iter() {
            buffer.extend(stmt.string());
        }
        buffer
    }
}

// Statement
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}
impl NodeInterface for Statement {
    fn get_node(&self) -> Node {
        Node::Statement(self)
    }

    fn token_literal(&self) -> Vec<ascii::Char> {
        match self {
            Self::Let(s) => s.token_literal(),
            Self::Return(s) => s.token_literal(),
            Self::Expression(s) => s.token_literal(),
        }
    }

    fn string(&self) -> Vec<ascii::Char> {
        match self {
            Self::Let(s) => s.string(),
            Self::Return(s) => s.string(),
            Self::Expression(s) => s.string(),
        }
    }
}

// LetStatement
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Expression,
}

impl LetStatement {
    pub fn new(token: Token, name: Identifier, value: Expression) -> Self {
        Self { token, name, value }
    }

    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            name: Identifier::empty(),
            value: Expression::empty(),
        }
    }
}

impl NodeInterface for LetStatement {
    fn get_node(&self) -> Node {
        Node::LetStatement(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();

        buffer.extend(self.token_literal());
        buffer.push(ascii::Char::Space);
        buffer.extend(self.name.string());
        buffer.extend([
            ascii::Char::Space,
            ascii::Char::EqualsSign,
            ascii::Char::Space,
        ]);
        buffer.extend(self.value.string());
        buffer.push(ascii::Char::Semicolon);

        buffer
    }
}

// ReturnStatement
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnStatement {
    pub token: Token,
    pub value: Expression,
}

impl ReturnStatement {
    pub fn new(token: Token, value: Expression) -> Self {
        Self { token, value }
    }
}

impl ReturnStatement {
    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            value: Expression::empty(),
        }
    }
}

impl NodeInterface for ReturnStatement {
    fn get_node(&self) -> Node {
        Node::ReturnStatement(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();

        buffer.extend(self.token_literal());
        buffer.push(ascii::Char::Space);
        buffer.extend(self.value.string());
        buffer.push(ascii::Char::Semicolon);

        buffer
    }
}

// ExpressionStatement
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionStatement {
    pub token: Token,
    pub value: Expression,
}

impl ExpressionStatement {
    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            value: Expression::empty(),
        }
    }
}

impl NodeInterface for ExpressionStatement {
    fn get_node(&self) -> Node {
        Node::ExpressionStatement(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        self.token.literal.clone()
    }

    fn string(&self) -> Vec<ascii::Char> {
        self.value.string()
    }
}

// Program
#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl Program {
    pub fn new() -> Self {
        Self {
            statements: Vec::new(),
        }
    }
}

impl NodeInterface for Program {
    fn get_node(&self) -> Node {
        Node::Program(self)
    }
    fn token_literal(&self) -> Vec<ascii::Char> {
        match self.statements.first() {
            Some(stmt) => stmt.token_literal(),
            None => Vec::new(),
        }
    }

    fn string(&self) -> Vec<ascii::Char> {
        let mut buffer = Vec::new();

        for s in self.statements.iter() {
            buffer.extend(s.string());
        }

        buffer
    }
}

// #[cfg(test)]
mod test {
    use crate::ast::{Expression, Identifier, LetStatement, NodeInterface, Statement};
    use crate::token::{Token, TokenKind};

    use super::Program;

    #[test]
    fn test_string1() {
        let mut program = Program {
            statements: vec![Statement::Let(LetStatement {
                token: Token {
                    kind: TokenKind::Let,
                    literal: "let".as_ascii().unwrap().to_vec(),
                },
                name: Identifier {
                    token: Token {
                        kind: TokenKind::Ident,
                        literal: "myVar".as_ascii().unwrap().to_vec(),
                    },
                    value: "myVar".as_ascii().unwrap().to_vec(),
                },
                value: Expression::Identifier(Identifier {
                    token: Token {
                        kind: TokenKind::Ident,
                        literal: "anotherVar".as_ascii().unwrap().to_vec(),
                    },
                    value: "anotherVar".as_ascii().unwrap().to_vec(),
                }),
            })],
        };

        if program.string() != "let myVar = anotherVar;".as_ascii().unwrap() {
            panic!(
                "program.string() wrong. expected: \"let myVar = anotherVar;\", got: \"{}\"",
                program.string().as_str()
            );
        }
    }
}
