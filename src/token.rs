use std::ops::Range;
use std::rc::Rc;

displayable_enum! {
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum TokenValue {
        Ident(ident: Rc<String>): "{ident}",
        True: "true",
        False: "false",
        If: "if",
        Then: "then",
        Else: "else",
        Nat(n: usize): "{n}",
        Succ: "succ",
        Pred: "pred",
        IsZero: "iszero",
        Lambda: "λ",
        Dot: ".",
        LParen: "(",
        RParen: ")",
        Eq: "=",
        EOF: "<EOF>"
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