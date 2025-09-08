use std::fmt;
use std::rc::Rc;
use std::str::FromStr;

use crate::parser::ParseError;
use crate::pretty_printer::PrettyPrinter;
use std::ops::Range;

displayable_enum! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum PrimitiveValue {
        True: "true",
        False: "false",
        Zero: "0"
    }
}

displayable_enum! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum PrimitiveFunction {
        Succ: "succ",
        Pred: "pred",
        IsZero: "iszero"
    }
}

displayable_enum! {
    /// AST for untyped lambda calculus
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum Expr {
        PrimVal(prim: PrimitiveValue, span: Range<usize>): "{prim}",
        PrimFunc(func: PrimitiveFunction, span: Range<usize>): "{func}",
        Var(name: Rc<String>, span: Range<usize>): "{name}",
        Abs(param: Rc<String>, body: Box<Self>, start: usize): "λ{param}.{body}",
        App(func: Box<Self>, arg: Box<Self>): f => {
            if func.is_greedy() {
                write!(f, "({func})")?;
            } else {
                write!(f, "{func}")?;
            }
            if matches!(arg.as_ref(), Expr::App(..)) {
                write!(f, " ({arg})")?;
            } else {
                write!(f, " {arg}")?;
            }
            Ok(())
        },
        Cond(cond: Box<Self>, then_br: Box<Self>, else_br: Box<Self>, start: usize): "if {cond} then {then_br} else {else_br}"
    }
}

displayable_enum! {
    /// Top-level statements: definitions or expressions
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum Stmt {
        Def(name: Rc<String>, expr: Expr): "{name} = {expr}",
        Expr(expr: Expr): "{expr}"
    }
}

impl From<Expr> for Stmt {
    fn from(e: Expr) -> Self {
        Stmt::Expr(e)
    }
}

impl Expr {

    // Whether the last expression takes following expressions until the end of the current level
    fn is_greedy(&self) -> bool {
        match self {
            Self::Abs(..) | Self::Cond(..) => true,
            Self::App(_, arg) => matches!(arg.as_ref(), Self::Abs(..) | Self::Cond(..)),
            _ => false
        }
    }

    fn span(&self) -> Range<usize> {
        match self {
            Self::PrimVal(_, span) | Self::PrimFunc(_, span) | Self::Var(_, span) => span.clone(),
            Self::Abs(_, tail, start) | Self::Cond(_, _, tail, start) => *start..tail.span().end,
            Self::App(func, arg) => func.span().start..arg.span().end
        }
    }

    /// Analyze variable binding: produce an `AnalyzedExpr` where each variable is
    /// labeled `Free` or `Bound(name, debruijn_index)` (index counts binders
    /// between occurrence and its binder).
    pub fn analyze(&self) -> Result<AnalyzedExpr, ParseError> {
        fn helper(expr: &Expr, ctx: &mut Vec<Rc<String>>) -> Result<AnalyzedExpr, ParseError> {
            match expr {
                Expr::PrimFunc(..) => Err(ParseError::new("Primitive function should be applied to an argument", expr.span())),
                Expr::PrimVal(prim, _) => Ok(AnalyzedExpr::PrimVal(*prim)),
                Expr::Var(name, _) => {
                    if let Some(pos) = ctx.iter().rposition(|n| n.as_ref() == name.as_ref()) {
                        let idx = ctx.len() - pos - 1;
                        Ok(AnalyzedExpr::Bound(Rc::clone(name), idx))
                    } else {
                        Ok(AnalyzedExpr::Free(Rc::clone(name)))
                    }
                }
                Expr::Abs(param, body, _) => {
                    ctx.push(Rc::clone(param));
                    let analyzed_body = helper(body.as_ref(), ctx)?;
                    ctx.pop();
                    Ok(AnalyzedExpr::Abs(Rc::clone(param), Box::new(analyzed_body)))
                }
                Expr::App(func, arg) =>
                    if let Expr::PrimFunc(func, _) = func.as_ref() {
                        Ok(AnalyzedExpr::PrimApp(*func, Box::new(helper(arg.as_ref(), ctx)?)))
                    } else {
                        Ok(AnalyzedExpr::App(Box::new(helper(func.as_ref(), ctx)?), Box::new(helper(arg.as_ref(), ctx)?)))
                    }
                Expr::Cond(cond, then_br, else_br, _) =>
                    Ok(
                        AnalyzedExpr::Cond(
                            Box::new(helper(cond.as_ref(), ctx)?),
                            Box::new(helper(then_br.as_ref(), ctx)?),
                            Box::new(helper(else_br.as_ref(), ctx)?),
                        )
                    )
            }
        }
        helper(self, &mut Vec::new())
    }
}

displayable_enum! {
    /// Analyzed AST where variables are labeled Free or Bound(name, debruijn_index)
    #[derive(Clone, PartialEq, Eq)]
    pub enum AnalyzedExpr {
        PrimVal(prim: PrimitiveValue): "{prim}",
        Free(name: Rc<String>): "{name}",
        Bound(name: Rc<String>, index: usize): "{name}#{index}",
        Abs(param: Rc<String>, body: Box<Self>): "λ{param}.{body}",
        App(func: Box<Self>, arg: Box<Self>): f => {
            if func.is_greedy() {
                write!(f, "({func})")?;
            } else {
                write!(f, "{func}")?;
            }
            if arg.is_func() {
                write!(f, " ({arg})")?;
            } else {
                write!(f, " {arg}")?;
            }
            Ok(())
        },
        PrimApp(func: PrimitiveFunction, arg: Box<Self>): f => {
            if arg.is_func() {
                write!(f, "{func} ({arg})")
            } else {
                write!(f, "{func} {arg}")
            }
        },
        Cond(cond: Box<Self>, then_br: Box<Self>, else_br: Box<Self>): "if {cond} then {then_br} else {else_br}"
    }
}

#[derive(Debug)]
pub struct EvaluationError {
    pub message: String
}

impl EvaluationError {
    pub fn new(msg: impl Into<String>) -> Self {
        Self { message: msg.into() }
    }
}

thread_local! {
    static EMPTY: AnalyzedExpr = AnalyzedExpr::Free(Rc::default());
}

impl Default for AnalyzedExpr {
    fn default() -> Self {
        EMPTY.with(|e| e.clone())
    }
}

impl fmt::Debug for AnalyzedExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print(&mut PrettyPrinter::new(f, 2))
    }
}

impl AnalyzedExpr {

    fn is_greedy(&self) -> bool {
        match self {
            Self::Abs(..) | Self::Cond(..) => true,
            Self::App(_, arg) | Self::PrimApp(_, arg) =>
                matches!(arg.as_ref(), Self::Abs(..) | Self::Cond(..)),
            _ => false
        }
    }

    fn is_func(&self) -> bool {
        matches!(self, Self::App(..) | Self::PrimApp(..))
    }

    fn is_value(&self) -> bool {
        match self {
            Self::Bound(..) => false,
            Self::App(func, arg) => matches!(func.as_ref(), Self::Free(..)) && arg.is_value(),
            Self::PrimApp(..) => self.get_number_value().is_some(),
            Self::Cond(cond, ..) => matches!(cond.as_ref(), Self::Free(..)),
            _ => true
        }
    }

    pub fn get_number_value(&self) -> Option<usize> {
        match self {
            Self::PrimVal(PrimitiveValue::Zero) => Some(0),
            Self::PrimApp(PrimitiveFunction::Succ, arg) => arg.get_number_value().map(|n| n + 1),
            _ => None
        }
    }

    fn print(&self, printer: &mut PrettyPrinter) -> fmt::Result {
        match self {
            Self::PrimVal(p) => {
                printer.print_entry("PrimVal")?;
                printer.push('(')?;
                printer.print_entry(format!("{}", p))?;
                printer.pop(')')
            }
            Self::Free(n) => {
                printer.print_entry("Free")?;
                printer.push('(')?;
                printer.print_entry(format!("{}", n))?;
                printer.pop(')')
            }
            Self::Bound(n, i) => {
                printer.print_entry("Bound")?;
                printer.push('(')?;
                printer.print_entry(format!("{}", n))?;
                printer.print_entry(format!("{}", i))?;
                printer.pop(')')
            }
            Self::Abs(p, b) => {
                printer.print_entry("Abs")?;
                printer.push('(')?;
                printer.print_entry(format!("{}", p))?;
                b.print(printer)?;
                printer.pop(')')
            }
            Self::App(f, a) => {
                printer.print_entry("App")?;
                printer.push('(')?;
                f.print(printer)?;
                a.print(printer)?;
                printer.pop(')')
            }
            Self::PrimApp(func, arg) => {
                printer.print_entry("PrimApp")?;
                printer.push('(')?;
                printer.print_entry(format!("{}", func))?;
                arg.print(printer)?;
                printer.pop(')')
            }
            Self::Cond(c, t, e) => {
                printer.print_entry("Cond")?;
                printer.push('(')?;
                c.print(printer)?;
                t.print(printer)?;
                e.print(printer)?;
                printer.pop(')')
            }
        }
    }

    /// Shift (in-place): modify self by shifting bound indices by d for indices >= cutoff
    fn shift(&mut self, d: isize, cutoff: usize) {
        match self {
            Self::Bound(_, k) => {
                if *k >= cutoff {
                    let nk_signed = (*k as isize) + d;
                    if nk_signed < 0 {
                        panic!("shift produced negative index");
                    }
                    *k = nk_signed as usize;
                }
            }
            Self::Abs(_, body) => body.shift(d, cutoff + 1),
            Self::App(f, a) => {
                f.shift(d, cutoff);
                a.shift(d, cutoff);
            }
            Self::PrimApp(_, a) => a.shift(d, cutoff),
            Self::Cond(c, t, e) => {
                c.shift(d, cutoff);
                t.shift(d, cutoff);
                e.shift(d, cutoff);
            }
            _ => {}
        }
    }

    // In-place substitute: replace occurrences of bound index j+cutoff with clonings of `s` shifted by cutoff
    fn subst(&mut self, j: usize, s: &Self, cutoff: usize) {
        match self {
            Self::Bound(_, k) => {
                if *k == j + cutoff {
                    // replace with s shifted by cutoff
                    let mut repl = s.clone();
                    repl.shift(cutoff as isize, 0);
                    *self = repl;
                }
            }
            Self::Abs(_, body) => body.subst(j, s, cutoff + 1),
            Self::App(f, a) => {
                f.subst(j, s, cutoff);
                a.subst(j, s, cutoff);
            }
            Self::PrimApp(_, a) => a.subst(j, s, cutoff),
            Self::Cond(c, t, e) => {
                c.subst(j, s, cutoff);
                t.subst(j, s, cutoff);
                e.subst(j, s, cutoff);
            }
            _ => {}
        }
    }

    // substitute at top (in-place): replace index 0 in body with val
    // Performs: v1 = val shifted by +1; subst 0 with v1 in-place; then shift result by -1
    fn substitute_top(&mut self, val: &Self) {
        let mut v1 = val.clone();
        v1.shift(1, 0);
        self.subst(0, &v1, 0);
        self.shift(-1, 0);
    }

    /// Substitute free variable occurrences of `name` with `val` in-place.
    /// This respects surrounding binders by shifting `val` by the current `cutoff` depth
    /// before inserting it, to maintain correct de Bruijn indices.
    fn substitute_free_inner(&mut self, name: &str, val: &Self, cutoff: usize) {
        match self {
            Self::Free(n) => {
                if n.as_ref() == name {
                    let mut repl = val.clone();
                    // shift cloned value by the current binder depth
                    repl.shift(cutoff as isize, 0);
                    *self = repl;
                }
            }
            Self::Abs(_, body) => body.substitute_free_inner(name, val, cutoff + 1),
            Self::App(f, a) => {
                f.substitute_free_inner(name, val, cutoff);
                a.substitute_free_inner(name, val, cutoff);
            }
            Self::PrimApp(_, a) => a.substitute_free_inner(name, val, cutoff),
            Self::Cond(c, t, e) => {
                c.substitute_free_inner(name, val, cutoff);
                t.substitute_free_inner(name, val, cutoff);
                e.substitute_free_inner(name, val, cutoff);
            }
            _ => {}
        }
    }

    /// Public wrapper: substitute free variable `name` throughout `self` with `val`.
    pub fn substitute_free(&mut self, name: &str, val: &Self) {
        self.substitute_free_inner(name, val, 0);
    }

    pub fn reduce(&mut self) -> Result<(), EvaluationError> {
        while !self.is_value() {
            self.reduce_step()?;
        }
        Ok(())
    }

    fn reduce_step(&mut self) -> Result<(), EvaluationError> {
        match self {
            Self::App(f, a) => {
                f.reduce()?;
                a.reduce()?;
                if let Self::Abs(_, body) = f.as_mut() {
                    let mut body_owned = std::mem::take(body);
                    let arg_owned = std::mem::take(a);
                    body_owned.substitute_top(&arg_owned);
                    *self = *body_owned;
                    Ok(())
                } else {
                    Err(EvaluationError::new("Expected lambda abstraction"))
                }
            }
            Self::PrimApp(PrimitiveFunction::Succ, a) => {
                a.reduce()?;
                if a.get_number_value().is_none() {
                    Err(EvaluationError::new("Expected number value"))
                } else {
                    Ok(())
                }
            }
            Self::PrimApp(PrimitiveFunction::Pred, a) => {
                a.reduce()?;
                match a.as_mut() {
                    Self::PrimApp(PrimitiveFunction::Succ, aa) if aa.get_number_value().is_some() => {
                        let aa_owned = std::mem::take(aa);
                        *self = *aa_owned;
                        return Ok(());
                    }
                    Self::PrimVal(PrimitiveValue::Zero) => {
                        *self = AnalyzedExpr::PrimVal(PrimitiveValue::Zero);
                        return Ok(());
                    }
                    _ => {
                        return Err(EvaluationError::new("Expected number value"));
                    }
                }
            }
            Self::PrimApp(PrimitiveFunction::IsZero, a) => {
                a.reduce()?;
                if a.get_number_value().is_none() {
                    Err(EvaluationError::new("Expected number value"))
                } else {
                    *self = if a.as_ref() == &AnalyzedExpr::PrimVal(PrimitiveValue::Zero) {
                        AnalyzedExpr::PrimVal(PrimitiveValue::True)
                    } else {
                        AnalyzedExpr::PrimVal(PrimitiveValue::False)
                    };
                    Ok(())
                }
            }
            Self::Cond(c, t, e) => {
                c.reduce()?;
                let b = match c.as_ref() {
                    AnalyzedExpr::PrimVal(PrimitiveValue::True) => {
                        t.reduce()?;
                        t
                    }
                    AnalyzedExpr::PrimVal(PrimitiveValue::False) => {
                        e.reduce()?;
                        e
                    }
                    _ => {
                        return Err(EvaluationError::new("Expected boolean value"));
                    }
                };
                let b_owned = std::mem::take(b);
                *self = *b_owned;
                Ok(())
            }
            Self::Bound(..) => Err(EvaluationError::new("Bound variable cannot appear outside of lambda abstraction")),
            _ => Ok(())
        }
    }
}

// --- Debug-format deserializer for `AnalyzedExpr` ---
// Parses strings like: Free("x"), Bound("x", 0), Abs("x", App(...)), App(..., ...)
struct DebugParser<'a> {
    s: &'a str,
    pos: usize,
}

impl<'a> DebugParser<'a> {
    fn new(s: &'a str) -> Self { Self { s, pos: 0 } }

    fn peek(&self) -> Option<char> { self.s[self.pos..].chars().next() }
    fn eat_char(&mut self) -> Option<char> {
        if let Some(ch) = self.peek() {
            self.pos += ch.len_utf8();
            Some(ch)
        } else { None }
    }
    fn skip_ws(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() { self.eat_char(); } else { break }
        }
    }

    fn expect_str(&mut self, literal: &str) -> Result<(), String> {
        self.skip_ws();
        if self.s[self.pos..].starts_with(literal) {
            self.pos += literal.len();
            Ok(())
        } else {
            Err(format!("expected '{}' at {}", literal, self.pos))
        }
    }

    fn parse_ident(&mut self) -> Result<String, String> {
        self.skip_ws();
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch == ',' || ch == ')' || ch.is_whitespace() { break; }
            self.eat_char();
        }
        if start == self.pos { return Err(format!("expected identifier at {}", start)); }
        Ok(self.s[start..self.pos].to_string())
    }

    fn parse_usize(&mut self) -> Result<usize, String> {
        self.skip_ws();
        let start = self.pos;
        while let Some(ch) = self.peek() { if ch.is_ascii_digit() { self.eat_char(); } else { break } }
        if start == self.pos { return Err(format!("expected number at {}", start)); }
    self.s[start..self.pos].parse::<usize>().map_err(|e| e.to_string())
    }

    fn parse_expr(&mut self) -> Result<AnalyzedExpr, String> {
        self.skip_ws();
        // variant name
        if self.s[self.pos..].starts_with("PrimVal") {
            self.expect_str("PrimVal(")?;
            let prim = self.parse_ident()?;
            self.skip_ws();
            self.expect_str(")")?;
            return Ok(AnalyzedExpr::PrimVal(prim.parse::<PrimitiveValue>()?));
        }
        if self.s[self.pos..].starts_with("Free") {
            self.expect_str("Free(")?;
            let name = self.parse_ident()?;
            self.skip_ws();
            self.expect_str(")")?;
            return Ok(AnalyzedExpr::Free(Rc::new(name)));
        }
        if self.s[self.pos..].starts_with("Bound") {
            self.expect_str("Bound(")?;
            let name = self.parse_ident()?;
            self.skip_ws();
            self.expect_str(",")?;
            self.skip_ws();
            let idx = self.parse_usize()?;
            self.skip_ws();
            self.expect_str(")")?;
            return Ok(AnalyzedExpr::Bound(Rc::new(name), idx));
        }
        if self.s[self.pos..].starts_with("Abs") {
            self.expect_str("Abs(")?;
            let name = self.parse_ident()?;
            self.skip_ws();
            self.expect_str(",")?;
            let body = self.parse_expr()?;
            self.skip_ws();
            self.expect_str(")")?;
            return Ok(AnalyzedExpr::Abs(Rc::new(name), Box::new(body)));
        }
        if self.s[self.pos..].starts_with("App") {
            self.expect_str("App(")?;
            let f = self.parse_expr()?;
            self.skip_ws();
            self.expect_str(",")?;
            let a = self.parse_expr()?;
            self.skip_ws();
            self.expect_str(")")?;
            return Ok(AnalyzedExpr::App(Box::new(f), Box::new(a)));
        }
        if self.s[self.pos..].starts_with("PrimApp") {
            self.expect_str("PrimApp(")?;
            let func = self.parse_ident()?;
            self.skip_ws();
            self.expect_str(",")?;
            let a = self.parse_expr()?;
            self.skip_ws();
            self.expect_str(")")?;
            return Ok(AnalyzedExpr::PrimApp(func.parse::<PrimitiveFunction>()?, Box::new(a)));
        }
        if self.s[self.pos..].starts_with("Cond") {
            self.expect_str("Cond(")?;
            let c = self.parse_expr()?;
            self.skip_ws();
            self.expect_str(",")?;
            let t = self.parse_expr()?;
            self.skip_ws();
            self.expect_str(",")?;
            let e = self.parse_expr()?;
            self.skip_ws();
            self.expect_str(")")?;
            return Ok(AnalyzedExpr::Cond(Box::new(c), Box::new(t), Box::new(e)));
        }
        Err(format!("unexpected token at {}", self.pos))
    }
}

impl FromStr for AnalyzedExpr {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = DebugParser::new(s);
        let e = p.parse_expr()?;
        p.skip_ws();
        if p.pos != s.len() { return Err(format!("trailing characters at {}", p.pos)); }
        Ok(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    fn parse_expr(s: impl AsRef<str>) -> Expr {
        if let Stmt::Expr(expr) = parser::parse(s).unwrap() {
            expr
        } else {
            panic!("expected expression");
        }
    }

    #[test]
    fn display_var() {
        let e = parse_expr("x");
        assert_eq!(e.to_string(), "x");
    }

    #[test]
    fn display_abs_app() {
        let lam = parse_expr("λz.x y");
        assert_eq!(lam.to_string(), "λz.x y");
    }

    #[test]
    fn display_nested_abs() {
        // λx.λy.x y
        let lam = parse_expr("λx.λy.x y");
        assert_eq!(lam.to_string(), "λx.λy.x y");
    }

    #[test]
    fn display_app_fun_is_abs() {
        // (λx.x) y
        let e = parse_expr("(λx.x) y");
        assert_eq!(e.to_string(), "(λx.x) y");
    }

    #[test]
    fn display_app_arg_is_app() {
        // a (b c)
        let e = parse_expr("a (b c)");
        assert_eq!(e.to_string(), "a (b c)");
    }

    #[test]
    fn display_app_fun_abs_and_arg_app() {
        // (λx.x) (a b)
        let e = parse_expr("(λx.x) (a b)");
        assert_eq!(e.to_string(), "(λx.x) (a b)");
    }

    #[test]
    fn beta_reduce_identity() {
        // (λx.x) y -> y
        let expr = parse_expr("(λx.x) y");
        let mut a = expr.analyze().unwrap();
        a.reduce().unwrap();
        let want = AnalyzedExpr::Free(Rc::new("y".into()));
        assert_eq!(a, want);
    }

    #[test]
    fn beta_reduce_nested() {
        // ((λx.λy.x) a) b -> a
        let expr = parse_expr("((λx.λy.x) a) b");
        let mut a = expr.analyze().unwrap();
        a.reduce().unwrap();
        let want = AnalyzedExpr::Free(Rc::new("a".into()));
        assert_eq!(a, want);
    }

    #[test]
    fn substitute_free_top_level() {
        // x y, substitute free x -> z  => z y
        let mut e = AnalyzedExpr::App(Box::new(AnalyzedExpr::Free(Rc::new("x".into()))), Box::new(AnalyzedExpr::Free(Rc::new("y".into()))));
        e.substitute_free("x", &AnalyzedExpr::Free(Rc::new("z".into())));
        let want = AnalyzedExpr::App(Box::new(AnalyzedExpr::Free(Rc::new("z".into()))), Box::new(AnalyzedExpr::Free(Rc::new("y".into()))));
        assert_eq!(e, want);
    }

    #[test]
    fn substitute_free_under_abs() {
        // λx. a x  with a -> λy.y  should become λx. (λy.y) x
        let mut e = AnalyzedExpr::Abs(
            Rc::new("x".into()),
            Box::new(AnalyzedExpr::App(
                Box::new(AnalyzedExpr::Free(Rc::new("a".into()))),
                Box::new(AnalyzedExpr::Bound(Rc::new("x".into()), 0)),
            )),
        );
        let val = AnalyzedExpr::Abs(Rc::new("y".into()), Box::new(AnalyzedExpr::Bound(Rc::new("y".into()), 0)));
        e.substitute_free("a", &val);
        let want = AnalyzedExpr::Abs(
            Rc::new("x".into()),
            Box::new(AnalyzedExpr::App(
                Box::new(AnalyzedExpr::Abs(Rc::new("y".into()), Box::new(AnalyzedExpr::Bound(Rc::new("y".into()), 0)))),
                Box::new(AnalyzedExpr::Bound(Rc::new("x".into()), 0)),
            )),
        );
        assert_eq!(e, want);
    }

    #[test]
    fn substitute_free_multiple() {
        // a b with a->c and b->d
        let mut e = AnalyzedExpr::App(Box::new(AnalyzedExpr::Free(Rc::new("a".into()))), Box::new(AnalyzedExpr::Free(Rc::new("b".into()))));
        e.substitute_free("a", &AnalyzedExpr::Free(Rc::new("c".into())));
        e.substitute_free("b", &AnalyzedExpr::Free(Rc::new("d".into())));
        let want = AnalyzedExpr::App(Box::new(AnalyzedExpr::Free(Rc::new("c".into()))), Box::new(AnalyzedExpr::Free(Rc::new("d".into()))));
        assert_eq!(e, want);
    }

    #[test]
    fn substitute_free_shift_behavior() {
        // Insert λy. y (has Bound 0) into depth 2: ensure bound indices adjusted correctly
        let mut ctx = AnalyzedExpr::Abs(
            Rc::new("a".into()),
            Box::new(AnalyzedExpr::Abs(
                Rc::new("b".into()),
                Box::new(AnalyzedExpr::App(Box::new(AnalyzedExpr::Free(Rc::new("x".into()))), Box::new(AnalyzedExpr::Bound(Rc::new("b".into()), 0)))),
            )),
        );
        // replace free x with (λy. y)
        let val = AnalyzedExpr::Abs(Rc::new("y".into()), Box::new(AnalyzedExpr::Bound(Rc::new("y".into()), 0)));
        ctx.substitute_free("x", &val);
        // expected: λa.λb. (λy.y) b
        let want = AnalyzedExpr::Abs(
            Rc::new("a".into()),
            Box::new(AnalyzedExpr::Abs(
                Rc::new("b".into()),
                Box::new(AnalyzedExpr::App(Box::new(AnalyzedExpr::Abs(Rc::new("y".into()), Box::new(AnalyzedExpr::Bound(Rc::new("y".into()), 0)))), Box::new(AnalyzedExpr::Bound(Rc::new("b".into()), 0)))),
            )),
        );
        assert_eq!(ctx, want);
    }

    #[test]
    fn call_by_value() {
        // id (id (λz.id z)) -> λz.id z
        let id = AnalyzedExpr::Abs(Rc::new("x".into()), Box::new(AnalyzedExpr::Bound(Rc::new("x".into()), 0)));
        let mut expr = AnalyzedExpr::App(
            Box::new(id.clone()),
            Box::new(AnalyzedExpr::App(
                Box::new(id.clone()),
                Box::new(AnalyzedExpr::Abs(
                    Rc::new("z".into()),
                    Box::new(AnalyzedExpr::App(
                        Box::new(id.clone()),
                        Box::new(AnalyzedExpr::Bound(Rc::new("z".into()), 0))
                    ))
                )),
            )),
        );
        expr.reduce().unwrap();
        let want = AnalyzedExpr::Abs(
            Rc::new("z".into()),
            Box::new(AnalyzedExpr::App(
                Box::new(id.clone()),
                Box::new(AnalyzedExpr::Bound(Rc::new("z".into()), 0)),
            )),
        );
        assert_eq!(expr, want);
    }

    #[test]
    fn analyze_free_bound() {
        // λx.x y -> Abs with Bound(x,#0) and Free(y)
        let lam = parse_expr("λx.x y");
        let a = lam.analyze().unwrap();
        let want = AnalyzedExpr::Abs(Rc::new("x".into()), Box::new(AnalyzedExpr::App(Box::new(AnalyzedExpr::Bound(Rc::new("x".into()), 0)), Box::new(AnalyzedExpr::Free(Rc::new("y".into()))))));
        assert_eq!(a, want);
    }

    #[test]
    fn analyze_nested_indices() {
        // λx.λy.x y -> Bound indices 1 and 0
        let lam_x = parse_expr("λx.λy.x y");
        let a = lam_x.analyze().unwrap();
        let want = AnalyzedExpr::Abs(
            Rc::new("x".into()),
            Box::new(AnalyzedExpr::Abs(
                Rc::new("y".into()),
                Box::new(AnalyzedExpr::App(Box::new(AnalyzedExpr::Bound(Rc::new("x".into()), 1)), Box::new(AnalyzedExpr::Bound(Rc::new("y".into()), 0)))),
            )),
        );
        assert_eq!(a, want);
    }
}
