use core::ascii;
use std::fmt::{Debug, Display};
use std::hash::Hash;

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
    IndexExpression(&'a IndexExpression),
    BlockStatement(&'a BlockStatement),
    Statement(&'a Statement),
    LetStatement(&'a LetStatement),
    ReturnStatement(&'a ReturnStatement),
    ExpressionStatement(&'a ExpressionStatement),
    Program(&'a Program),
    StringLiteral(&'a StringLiteral),
    ArrayLiteral(&'a ArrayLiteral),
    HashLiteral(&'a HashLiteral),
}

pub trait NodeInterface: Display + Debug {
    /// 実体がenumのNode、すなわちExpressionやStatementは、Node::Expression/Statementを返すのではなくて、ラップされているNodeを返す。
    /// 例えば、Expression(IntegerLiteral)に対してget_nodeを呼ぶと、Node::IntegerLiteralが返される。
    fn get_node(&self) -> Node;
    fn get_token(&self) -> Token;
}

// Expression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    ArrayLiteral(ArrayLiteral),
    IndexExpression(IndexExpression),
    HashLiteral(HashLiteral),
    BlockStatement(BlockStatement),
}

impl Expression {
    pub fn empty() -> Self {
        Self::Identifier(Identifier::empty())
    }

    fn as_interface(&self) -> &dyn NodeInterface {
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
            Self::ArrayLiteral(x) => x,
            Self::IndexExpression(x) => x,
            Self::HashLiteral(x) => x,
            Self::BlockStatement(x) => x,
        }
    }
}

impl NodeInterface for Expression {
    fn get_node(&self) -> Node {
        Node::Expression(self)
    }

    fn get_token(&self) -> Token {
        self.as_interface().get_token()
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_interface())
    }
}

// Identifier
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier {
    pub token: Token,
    pub value: String,
}
impl Identifier {
    pub fn new(token: Token, value: &str) -> Self {
        Self {
            token,
            value: value.to_string(),
        }
    }

    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            value: String::new(),
        }
    }
}

impl NodeInterface for Identifier {
    fn get_node(&self) -> Node {
        Node::Identifier(self)
    }

    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.as_str())
    }
}

// IntegerLiteral
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for IntegerLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// Boolean
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for BoolLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// StringLiteral
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StringLiteral {
    pub token: Token,
    pub value: String,
}

impl StringLiteral {
    pub fn new(token: Token, value: &str) -> Self {
        Self {
            token,
            value: value.to_string(),
        }
    }
}

impl NodeInterface for StringLiteral {
    fn get_node(&self) -> Node {
        Node::StringLiteral(self)
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for StringLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.value.as_str())
    }
}

// ArrayLiteral
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayLiteral {
    pub token: Token,
    pub elements: Vec<Expression>,
}

impl ArrayLiteral {
    pub fn new(token: Token, elements: &[Expression]) -> Self {
        Self {
            token,
            elements: elements.to_vec(),
        }
    }
}

impl NodeInterface for ArrayLiteral {
    fn get_node(&self) -> Node {
        Node::ArrayLiteral(self)
    }

    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for ArrayLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let elements = self
            .elements
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>();

        write!(f, "[{}]", elements.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HashLiteral {
    pub token: Token,
    pub pairs: Vec<(Expression, Expression)>,
}

impl HashLiteral {
    pub fn new(token: Token, pairs: Vec<(Expression, Expression)>) -> Self {
        Self { token, pairs }
    }
}

impl NodeInterface for HashLiteral {
    fn get_node(&self) -> Node {
        Node::HashLiteral(self)
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for HashLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pairs = self
            .pairs
            .iter()
            .map(|(k, v)| format!("{} : {}", k, v))
            .collect::<Vec<String>>();

        write!(f, "{{{}}}", pairs.join(", "))
    }
}

// PrefixExpression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PrefixExpression {
    pub token: Token,
    pub operator: String,
    pub right: Box<Expression>,
}

impl PrefixExpression {
    pub fn new(token: Token, operator: &str, right: Expression) -> Self {
        Self {
            token,
            operator: operator.to_string(),
            right: Box::new(right),
        }
    }

    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            operator: String::new(),
            right: Box::new(Expression::empty()),
        }
    }
}

impl NodeInterface for PrefixExpression {
    fn get_node(&self) -> Node {
        Node::PrefixExpression(self)
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for PrefixExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}{})", self.operator.as_str(), self.right)
    }
}

// InfixExpression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InfixExpression {
    pub token: Token,
    pub operator: String,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

impl InfixExpression {
    pub fn new(token: Token, operator: &str, left: Expression, right: Expression) -> Self {
        Self {
            token,
            operator: operator.to_string(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl NodeInterface for InfixExpression {
    fn get_node(&self) -> Node {
        Node::InfixExpression(self)
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for InfixExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} {} {})",
            self.left,
            self.operator.as_str(),
            self.right
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for IfExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = write!(f, "if ({}) {}", self.condition, self.consequence);

        if let Some(alternative) = &self.alternative {
            result = write!(f, " else {}", alternative);
        }

        result
    }
}

// FunctionLiteral
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for FunctionLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = self
            .params
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>();
        write!(f, "fn ({}) {}", params.join(", "), self.body)
    }
}

// CallExpression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for CallExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args = self
            .args
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>();
        write!(f, "{}({})", self.func, args.join(", "))
    }
}

// IndexExpression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IndexExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub index: Box<Expression>,
}

impl IndexExpression {
    pub fn new(token: Token, left: Expression, index: Expression) -> Self {
        Self {
            token,
            left: Box::new(left),
            index: Box::new(index),
        }
    }
}

impl NodeInterface for IndexExpression {
    fn get_node(&self) -> Node {
        Node::IndexExpression(self)
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for IndexExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}[{}])", self.left, self.index)
    }
}

// BlockStatement
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BlockStatement {
    pub token: Token,
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
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for BlockStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let statements = self
            .statements
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>();
        write!(f, "{{{}}}", statements.join(" "))
    }
}

// Statement

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

impl Statement {
    fn as_interface(&self) -> &dyn NodeInterface {
        match self {
            Self::Let(x) => x,
            Self::Return(x) => x,
            Self::Expression(x) => x,
        }
    }
}

impl NodeInterface for Statement {
    fn get_node(&self) -> Node {
        Node::Statement(self)
    }

    fn get_token(&self) -> Token {
        self.as_interface().get_token()
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Let(x) => write!(f, "{}", x),
            Self::Return(x) => write!(f, "{}", x),
            Self::Expression(x) => write!(f, "{}", x),
        }
    }
}

// LetStatement
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Expression,
    pub has_semicolon: bool,
}

impl LetStatement {
    pub fn new(token: Token, name: Identifier, value: Expression, has_semicolon: bool) -> Self {
        Self {
            token,
            name,
            value,
            has_semicolon,
        }
    }

    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            name: Identifier::empty(),
            value: Expression::empty(),
            has_semicolon: true,
        }
    }
}

impl NodeInterface for LetStatement {
    fn get_node(&self) -> Node {
        Node::LetStatement(self)
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for LetStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = write!(f, "let {} = {}", self.name, self.value);
        if self.has_semicolon {
            result = write!(f, ";");
        }
        result
    }
}

// ReturnStatement
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ReturnStatement {
    pub token: Token,
    pub value: Expression,
    pub has_semicolon: bool,
}

impl ReturnStatement {
    pub fn new(token: Token, value: Expression, has_semicolon: bool) -> Self {
        Self {
            token,
            value,
            has_semicolon,
        }
    }

    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            value: Expression::empty(),
            has_semicolon: true,
        }
    }
}

impl NodeInterface for ReturnStatement {
    fn get_node(&self) -> Node {
        Node::ReturnStatement(self)
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for ReturnStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = write!(f, "return {}", self.value);
        if self.has_semicolon {
            result = write!(f, ";");
        }
        result
    }
}

// ExpressionStatement
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExpressionStatement {
    pub token: Token,
    pub value: Expression,
    pub has_semicolon: bool,
}

impl ExpressionStatement {
    pub fn new(token: Token, value: Expression, has_semicolon: bool) -> Self {
        Self {
            token,
            value,
            has_semicolon,
        }
    }

    pub fn empty() -> Self {
        Self {
            token: Token::empty(),
            value: Expression::empty(),
            has_semicolon: true,
        }
    }
}

impl NodeInterface for ExpressionStatement {
    fn get_node(&self) -> Node {
        Node::ExpressionStatement(self)
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

impl Display for ExpressionStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = write!(f, "{}", self.value);
        if self.has_semicolon {
            result = write!(f, ";");
        }
        result
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
    fn get_token(&self) -> Token {
        self.statements[0].get_token()
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let statements = self
            .statements
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>();
        write!(f, "{}", statements.join(" "))
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
                    literal: "let".to_string(),
                },
                name: Identifier {
                    token: Token {
                        kind: TokenKind::Ident,
                        literal: "myVar".to_string(),
                    },
                    value: "myVar".to_string(),
                },
                value: Expression::Identifier(Identifier {
                    token: Token {
                        kind: TokenKind::Ident,
                        literal: "anotherVar".to_string(),
                    },
                    value: "anotherVar".to_string(),
                }),
                has_semicolon: true,
            })],
        };

        if program.to_string().as_str() != "let myVar = anotherVar;" {
            panic!(
                "program.string() wrong. expected: \"let myVar = anotherVar;\", got: \"{}\"",
                program.to_string().as_str()
            );
        }
    }
}
