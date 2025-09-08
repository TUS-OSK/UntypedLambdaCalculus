use std::ops::Range;

use ariadne::{Label, Report, ReportKind};

use crate::ast::Expr;
use crate::ast::PrimitiveFunction;
use crate::ast::PrimitiveValue;
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
    fn parse_statement(&mut self) -> Result<Stmt, ParseError> {
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
                let expr = self.parse_tailing_rec(Expr::Var(name, first_tok.span))?;
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
        match self.parse_atom()? {
            Some(right) => self.parse_tailing_rec(Expr::App(Box::new(left), Box::new(right))),
            None => return Ok(left),
        }
    }

    // A -> PrimVal | PrimFunc | Ident | Abs | Cond | (E)
    fn parse_atom(&mut self) -> Result<Option<Expr>, ParseError> {
        if let Some(expr) = self.parse_prim_val()? {
            return Ok(Some(expr));
        }
        if let Some(expr) = self.parse_prim_func()? {
            return Ok(Some(expr));
        }
        if let Some(expr) = self.parse_ident()? {
            return Ok(Some(expr));
        }
        if let Some(expr) = self.parse_cond()? {
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

    fn parse_prim_val(&mut self) -> Result<Option<Expr>, ParseError> {
        let tok = self.lexer.peek_token()?;
        let prim = match tok.value {
            TokenValue::True => PrimitiveValue::True,
            TokenValue::False => PrimitiveValue::False,
            TokenValue::Num(num) => {
                self.lexer.next_token()?;
                return Ok(Some(Self::expand_num(num, tok.span)));
            }
            _ => return Ok(None)
        };
        self.lexer.next_token()?;
        Ok(Some(Expr::PrimVal(prim, tok.span)))
    }

    fn expand_num(n: usize, span: Range<usize>) -> Expr {
        let mut expr = Expr::PrimVal(PrimitiveValue::Zero, span.clone());
        for _ in 0..n {
            expr = Expr::App(Box::new(Expr::PrimFunc(PrimitiveFunction::Succ, span.clone())), Box::new(expr));
        }
        expr
    }

    fn parse_prim_func(&mut self) -> Result<Option<Expr>, ParseError> {
        let tok = self.lexer.peek_token()?;
        let prim_func = match tok.value {
            TokenValue::Succ => PrimitiveFunction::Succ,
            TokenValue::Pred => PrimitiveFunction::Pred,
            TokenValue::IsZero => PrimitiveFunction::IsZero,
            _ => return Ok(None)
        };
        self.lexer.next_token()?;
        Ok(Some(Expr::PrimFunc(prim_func, tok.span)))
    }

    fn parse_ident(&mut self) -> Result<Option<Expr>, ParseError> {
        let tok = self.lexer.peek_token()?;
        match tok.value {
            TokenValue::Ident(name) => {
                self.lexer.next_token()?;
                Ok(Some(Expr::Var(name, tok.span)))
            }
            _ => Ok(None)
        }
    }

    fn parse_abs(&mut self) -> Result<Option<Expr>, ParseError> {
        if let Token { value: TokenValue::Lambda, span } = self.lexer.peek_token()? {
            self.lexer.next_token()?;
            let ident = match self.lexer.next_token()? {
                Token { value: TokenValue::Ident(name), .. } => name,
                Token { span, .. } => return Err(ParseError::new("Expected identifier after lambda", span)),
            };
            match self.lexer.next_token()? {
                Token { value: TokenValue::Dot, .. } => {},
                Token { span, .. } => return Err(ParseError::new("Expected '.' after lambda parameter", span)),
            }
            Ok(Some(Expr::Abs(ident, Box::new(self.parse_expr()?), span.start)))
        } else {
            Ok(None)
        }
    }

    fn parse_cond(&mut self) -> Result<Option<Expr>, ParseError> {
        if let Token { value: TokenValue::If, span } = self.lexer.peek_token()? {
            self.lexer.next_token()?;
            let cond = self.parse_expr()?;
            match self.lexer.next_token()? {
                Token { value: TokenValue::Then, .. } => {},
                Token { span, .. } => return Err(ParseError::new("Expected 'then' after condition", span)),
            }
            let then_branch = self.parse_expr()?;
            match self.lexer.next_token()? {
                Token { value: TokenValue::Else, .. } => {},
                Token { span, .. } => return Err(ParseError::new("Expected 'else' after then-branch", span)),
            }
            let else_branch = self.parse_expr()?;
            Ok(Some(Expr::Cond(Box::new(cond), Box::new(then_branch), Box::new(else_branch), span.start)))
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
        let want = Expr::Var(Rc::new("x".to_string()), 0..1);
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_lambda() {
        let e = parse("λx.x").unwrap();
        let want = Expr::Abs(Rc::new("x".into()), Box::new(Expr::Var(Rc::new("x".into()), 3..4)), 0);
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_app_left_assoc() {
        // x y z -> ((x y) z)
        let e = parse("x y z").unwrap();
        let x = Expr::Var(Rc::new("x".into()), 0..1);
        let y = Expr::Var(Rc::new("y".into()), 2..3);
        let z = Expr::Var(Rc::new("z".into()), 4..5);
        let want = Expr::App(Box::new(Expr::App(Box::new(x), Box::new(y))), Box::new(z));
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_paren_grouping() {
        // (x y) z -> ((x y) z)
        let e = parse("(x y) z").unwrap();
        let x = Expr::Var(Rc::new("x".into()), 1..2);
        let y = Expr::Var(Rc::new("y".into()), 3..4);
        let z = Expr::Var(Rc::new("z".into()), 6..7);
        let want = Expr::App(Box::new(Expr::App(Box::new(x), Box::new(y))), Box::new(z));
        assert_eq!(e, want.into());
    }

    #[test]
    fn parse_definition_statement() {
        let mut p = Parser::new(Lexer::new("id = λx.x"));
        match p.parse_statement().unwrap() {
            Stmt::Def(name, expr) => {
                assert_eq!(name.as_ref(), "id");
                assert_eq!(expr.to_string(), "λx.x");
            }
            _ => panic!("expected definition"),
        }
    }
}