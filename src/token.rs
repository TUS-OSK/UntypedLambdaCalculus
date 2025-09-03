use std::fmt::{self, Display, Formatter};
use std::ops::Range;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenValue {
    Ident(Rc<String>),
    Lambda,
    Dot,
    LParen,
    RParen,
    Eq,
    ChurchNumber(u32),
    EOF
}

impl Display for TokenValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TokenValue::Ident(name) => write!(f, "{}", name),
            TokenValue::Lambda => write!(f, "λ"),
            TokenValue::Dot => write!(f, "."),
            TokenValue::LParen => write!(f, "("),
            TokenValue::RParen => write!(f, ")"),
            TokenValue::Eq => write!(f, "="),
            TokenValue::ChurchNumber(n) => write!(f, "c{}", n),
            TokenValue::EOF => write!(f, "<EOF>"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub value: TokenValue,
    pub span: Range<usize>,
}

impl Token {
    pub fn new(value: TokenValue, span: Range<usize>) -> Self {
        Self { value, span }
    }
}