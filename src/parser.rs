use std::ops::Range;

use ariadne::{Label, Report, ReportKind};

use crate::ast::Expr;
use crate::ast::Stmt;
use crate::lexer::Lexer;
use crate::token::{Token, TokenValue};

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
    pub span: Range<usize>
}

impl ParseError {
    pub fn new(msg: impl Into<String>, span: Range<usize>) -> Self {
        Self { message: msg.into(), span }
    }

    pub fn report(&self) -> Report<'_> {
        Report::build(ReportKind::Error, self.span.clone())
            .with_message(&self.message)
            .with_label(
                Label::new(self.span.clone())
                    .with_message("here")
                    .with_color(ariadne::Color::Red)
            )
            .finish()
    }
}

pub fn parse(input: impl AsRef<str>) -> Result<Stmt, ParseError> {
    Parser::new(Lexer::new(input)).parse()
}

pub struct Parser {
    lexer: Lexer
}

impl Parser {

    pub fn new(lexer: Lexer) -> Self {
        Self { lexer }
    }

    pub fn parse(&mut self) -> Result<Stmt, ParseError> {
        let stmt = self.parse_statement();
        if self.lexer.peek_token()?.value == TokenValue::EOF {
            stmt
        } else {
            Err(ParseError::new("Expected EOF", self.lexer.peek_token()?.span))
        }
    }

    /// Parse a top-level statement: either a definition `name = expr` or an expression
    pub fn parse_statement(&mut self) -> Result<Stmt, ParseError> {
        // Peek first token
        let first_tok = self.lexer.peek_token()?;
        match first_tok.value {
            TokenValue::Ident(name) => {
                // consume identifier
                self.lexer.next_token()?;
                // If next token is '=', parse definition
                if let Token { value: TokenValue::Eq, .. } = self.lexer.peek_token()? {
                    self.lexer.next_token()?; // consume '='
                    let expr = self.parse_expr()?;
                    return Ok(Stmt::Def(name, expr));
                }

                // Not a definition — treat the consumed identifier as first atom and parse remaining application
                let expr = self.parse_tailing_rec(Expr::Var(name))?;
                Ok(Stmt::Expr(expr))
            }
            _ => {
                // parse as an expression statement
                let expr = self.parse_expr()?;
                Ok(Stmt::Expr(expr))
            }
        }
    }

    // E -> A E'
    fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        match self.parse_atom()? {
            Some(first) => self.parse_tailing_rec(first),
            None => {
                Err(ParseError::new("Expected expression", self.lexer.peek_token()?.span))
            }
        }
    }

    // E' -> A E' | ε
    fn parse_tailing_rec(&mut self, left: Expr) -> Result<Expr, ParseError> {
        let right = match self.parse_atom()? {
            Some(expr) => expr,
            None => return Ok(left),
        };
        self.parse_tailing_rec(Expr::App(Box::new(left), Box::new(right)))
    }

    // A -> Ident | ChurchNumber | App | (E)
    fn parse_atom(&mut self) -> Result<Option<Expr>, ParseError> {
        if let Some(expr) = self.parse_ident()? {
            return Ok(Some(expr));
        }
        if let Some(expr) = self.parse_church_number()? {
            return Ok(Some(expr));
        }
        if let Some(expr) = self.parse_abs()? {
            return Ok(Some(expr));
        }
        if let Some(expr) = self.parse_paren()? {
            return Ok(Some(expr));
        }
        Ok(None)
    }

    fn parse_ident(&mut self) -> Result<Option<Expr>, ParseError> {
        match self.lexer.peek_token()?.value {
            TokenValue::Ident(name) => {
                self.lexer.next_token()?;
                Ok(Some(Expr::Var(name)))
            }
            _ => Ok(None)
        }
    }

    fn parse_church_number(&mut self) -> Result<Option<Expr>, ParseError> {
        match self.lexer.peek_token()?.value {
            TokenValue::ChurchNumber(n) => {
                self.lexer.next_token()?;
                Ok(Some(Expr::church_numeral(n)))
            }
            _ => Ok(None)
        }
    }

    fn parse_abs(&mut self) -> Result<Option<Expr>, ParseError> {
        if let TokenValue::Lambda = self.lexer.peek_token()?.value {
            self.lexer.next_token()?;
            let ident = match self.lexer.next_token()? {
                Token { value: TokenValue::Ident(name), .. } => name,
                Token { span, .. } => return Err(ParseError::new("Expected identifier after lambda", span)),
            };
            match self.lexer.next_token()? {
                Token { value: TokenValue::Dot, .. } => {},
                Token { span, .. } => return Err(ParseError::new("Expected '.' after lambda parameter", span)),
            }
            Ok(Some(Expr::Abs(ident, Box::new(self.parse_expr()?))))
        } else {
            Ok(None)
        }
    }

    fn parse_paren(&mut self) -> Result<Option<Expr>, ParseError> {
        if let Token { value: TokenValue::LParen, .. } = self.lexer.peek_token()? {
            self.lexer.next_token()?;
            let expr = self.parse_expr()?;
            match self.lexer.next_token()? {
                Token { value: TokenValue::RParen, .. } => Ok(Some(expr)),
                Token { span, .. } => Err(ParseError::new("Expected ')' after expression", span))
            }
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Expr;
    use std::rc::Rc;

    #[test]
    fn parse_var() {
        let e = parse("x").unwrap();
        let want = Expr::Var(Rc::new("x".to_string()));
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_lambda() {
        let e = parse("λx.x").unwrap();
        let want = Expr::Abs(Rc::new("x".into()), Box::new(Expr::Var(Rc::new("x".into()))));
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_app_left_assoc() {
        // x y z -> ((x y) z)
        let e = parse("x y z").unwrap();
        let x = Expr::Var(Rc::new("x".into()));
        let y = Expr::Var(Rc::new("y".into()));
        let z = Expr::Var(Rc::new("z".into()));
        let want = Expr::App(Box::new(Expr::App(Box::new(x), Box::new(y))), Box::new(z));
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_paren_grouping() {
        // (x y) z -> ((x y) z)
        let e = parse("(x y) z").unwrap();
        let x = Expr::Var(Rc::new("x".into()));
        let y = Expr::Var(Rc::new("y".into()));
        let z = Expr::Var(Rc::new("z".into()));
        let want = Expr::App(Box::new(Expr::App(Box::new(x), Box::new(y))), Box::new(z));
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_church_numbers() {
        // c0 should parse as λf.λx.x
        let e = parse("c0").unwrap();
        let want = Expr::church_numeral(0);
        assert_eq!(e, want.into());

        // c2 should parse as λf.λx.f (f x)
        let e = parse("c2").unwrap();
        let want = Expr::church_numeral(2);
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_church_numbers_in_application() {
        // c1 c2 should parse as application of church numerals
        let e = parse("c1 c2").unwrap();
        let c1 = Expr::church_numeral(1);
        let c2 = Expr::church_numeral(2);
        let want = Expr::App(Box::new(c1), Box::new(c2));
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_definition_statement() {
        let mut p = Parser::new(Lexer::new("id = λx.x"));
        match p.parse_statement().unwrap() {
            Stmt::Def(name, expr) => {
                assert_eq!(&*name, "id");
                assert_eq!(expr.to_string(), "λx.x");
            }
            _ => panic!("expected definition"),
        }
    }
}