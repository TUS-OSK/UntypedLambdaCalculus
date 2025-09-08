use std::rc::Rc;

use crate::parser::ParseError;
use crate::token::{Token, TokenValue};

pub struct Lexer {
    input: Vec<char>,
    pos: usize,
    peeked: Option<Token>,
}

impl Lexer {
    pub fn new(s: impl AsRef<str>) -> Self {
        Lexer { input: s.as_ref().chars().collect(), pos: 0, peeked: None }
    }

    /// Peek the next tok without advancing the lexer's position.
    /// Returns the token and the position after it, or None at EOF.
    pub fn peek_token(&mut self) -> Result<Token, ParseError> {
        // return cached if available
        if let Some(tok) = &self.peeked {
            return Ok(tok.clone());
        }

        let len = self.input.len();
        let mut i = self.pos;

        // skip whitespace
        while i < len && self.input[i].is_whitespace() {
            i += 1;
        }

        if i >= len {
            let tok = Token::new(TokenValue::EOF, i..i);
            self.peeked = Some(tok.clone());
            return Ok(tok);
        }

        let token_value = match self.input[i] {
            'λ' => TokenValue::Lambda,
            '(' => TokenValue::LParen,
            ')' => TokenValue::RParen,
            '.' => TokenValue::Dot,
            '=' => TokenValue::Eq,
            c if c.is_alphabetic() || c == '_' => {
                let start = i;
                while i < len {
                    let cc = self.input[i];
                    if cc.is_alphanumeric() || cc == '_' {
                        i += 1;
                    } else {
                        break;
                    }
                }
                let s = self.input[start..i].iter().collect::<String>();
                let tok_val = match s.as_ref() {
                    "true" => TokenValue::True,
                    "false" => TokenValue::False,
                    "if" => TokenValue::If,
                    "then" => TokenValue::Then,
                    "else" => TokenValue::Else,
                    "succ" => TokenValue::Succ,
                    "pred" => TokenValue::Pred,
                    "iszero" => TokenValue::IsZero,
                    _ => TokenValue::Ident(Rc::new(s))
                };
                let tok = Token::new(tok_val, start..i);
                self.peeked = Some(tok.clone());
                return Ok(tok);
            }
            c if c.is_ascii_digit() => {
                let start = i;
                let mut num: usize = 0;
                while i < len {
                    let cc = self.input[i];
                    if cc.is_ascii_digit() {
                        i += 1;
                        num = num * 10 + (cc.to_digit(10).unwrap() as usize);
                    } else {
                        break;
                    }
                }
                let tok = Token::new(TokenValue::Nat(num), start..i);
                self.peeked = Some(tok.clone());
                return Ok(tok);
            }
            _ => {
                return Err(ParseError::new("Unexpected character", i..i));
            }
        };
        i += 1;
        let tok = Token::new(token_value, i - 1..i);
        self.peeked = Some(tok.clone());
        Ok(tok) 
    }

    /// Return the next token. Returns Err on unexpected characters.
    pub fn next_token(&mut self) -> Result<Token, ParseError> {
        let tok = self.peek_token()?;
        self.peeked = None;
        self.pos = tok.span.end;
        Ok(tok)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(s: impl AsRef<str>) -> Result<Vec<Token>, ParseError> {
        let mut lex = Lexer::new(s);
        let mut out = Vec::new();
        loop {
            let tok = lex.next_token()?;
            if tok.value == TokenValue::EOF {
                break;
            }
            out.push(tok);
        }
        Ok(out)
    }

    #[test]
    fn tokenize_unicode_lambda() {
        let toks = tokenize("λx.x").unwrap();
        let s: Vec<String> = toks.iter().map(|t| t.value.to_string()).collect();
        assert_eq!(s, vec!["λ", "x", ".", "x"]);
    }

    #[test]
    fn tokenize_lambda_and_greek() {
        let toks = tokenize("λα.α").unwrap();
        let s: Vec<String> = toks.iter().map(|t| t.value.to_string()).collect();
        assert_eq!(s, vec!["λ", "α", ".", "α"]);
    }

    #[test]
    fn tokenize_with_whitespace() {
        let toks = tokenize("  λ  x  .   y  ").unwrap();
        let s: Vec<String> = toks.iter().map(|t| t.value.to_string()).collect();
        assert_eq!(s, vec!["λ", "x", ".", "y"]);
    }

    #[test]
    fn ident_does_not_start_with_digit() {
        // Inputs without invalid leading digits should succeed
        let toks = tokenize("x x2 _3 a1").unwrap();
        let s: Vec<String> = toks.iter().map(|t| t.value.to_string()).collect();
        assert_eq!(s, vec!["x", "x2", "_3", "a1"]);

        // Inputs with leading digits should produce an error
        let res = tokenize("1x x2 _3");
        assert!(res.is_err());
    }
}