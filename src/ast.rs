use std::fmt::{self, Display};
use std::rc::Rc;

/// Simple AST for untyped lambda calculus
/// Expr = Var(name) | Abs(param, body) | App(func, arg)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(Rc<String>),
    Abs(Rc<String>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

impl Default for Expr {
    fn default() -> Self {
        Expr::Var(Rc::default())
    }
}

/// Top-level statements: definitions or expressions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Def(Rc<String>, Expr),
    Expr(Expr),
}

impl Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Def(name, expr) => write!(f, "{} = {}", name, expr),
            Stmt::Expr(e) => write!(f, "{}", e),
        }
    }
}

impl From<Expr> for Stmt {
    fn from(e: Expr) -> Self {
        Stmt::Expr(e)
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(name) => write!(f, "{}", name),
            Self::Abs(param, body) => write!(f, "λ{}.{}", param, body),
            Self::App(fun, arg) => {
                let fun_needs_paren = matches!(fun.as_ref(), Self::Abs(..));
                let arg_needs_paren = arg.contains_app();

                if fun_needs_paren && arg_needs_paren {
                    write!(f, "({}) ({})", fun, arg)
                } else if fun_needs_paren {
                    write!(f, "({}) {}", fun, arg)
                } else if arg_needs_paren {
                    write!(f, "{} ({})", fun, arg)
                } else {
                    write!(f, "{} {}", fun, arg)
                }
            }
        }
    }
}

impl Expr {

    fn contains_app(&self) -> bool {
        match self {
            Self::Var(_) => false,
            Self::Abs(_, body) => body.contains_app(),
            Self::App(_, _) => true,
        }
    }

    /// Analyze variable binding: produce an `AnalyzedExpr` where each variable is
    /// labeled `Free` or `Bound(name, debruijn_index)` (index counts binders
    /// between occurrence and its binder).
    pub fn analyze(&self) -> AnalyzedExpr {
        fn helper(expr: &Expr, ctx: &mut Vec<Rc<String>>) -> AnalyzedExpr {
            match expr {
                Expr::Var(name) => {
                    if let Some(pos) = ctx.iter().rposition(|n| n.as_ref() == name.as_ref()) {
                        let idx = ctx.len() - pos - 1;
                        AnalyzedExpr::Bound(name.clone(), idx)
                    } else {
                        AnalyzedExpr::Free(name.clone())
                    }
                }
                Expr::Abs(param, body) => {
                    ctx.push(param.clone());
                    let b = helper(body.as_ref(), ctx);
                    ctx.pop();
                    AnalyzedExpr::Abs(param.clone(), Box::new(b))
                }
                Expr::App(f, a) => AnalyzedExpr::App(Box::new(helper(f.as_ref(), ctx)), Box::new(helper(a.as_ref(), ctx))),
            }
        }
        helper(self, &mut Vec::new())
    }
}

/// Analyzed AST where variables are labeled Free or Bound(name, debruijn_index)
#[derive(Clone, PartialEq, Eq)]
pub enum AnalyzedExpr {
    Free(Rc<String>),
    Bound(Rc<String>, usize),
    Abs(Rc<String>, Box<AnalyzedExpr>),
    App(Box<AnalyzedExpr>, Box<AnalyzedExpr>),
}

impl Default for AnalyzedExpr {
    fn default() -> Self {
        AnalyzedExpr::Free(Rc::default())
    }
}

impl fmt::Debug for AnalyzedExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AnalyzedExpr::Free(n) => write!(f, "Free({})", n),
            AnalyzedExpr::Bound(n, i) => write!(f, "Bound({}, #{})", n, i),
            AnalyzedExpr::Abs(p, b) => write!(f, "Abs({}, {:?})", p, b),
            AnalyzedExpr::App(fun, arg) => write!(f, "App({:?}, {:?})", fun, arg),
        }
    }
}

impl Display for AnalyzedExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AnalyzedExpr::Free(n) => write!(f, "{}", n),
            AnalyzedExpr::Bound(n, i) => write!(f, "{}#{}", n, i),
            AnalyzedExpr::Abs(p, b) => write!(f, "λ{}.{}", p, b),
            AnalyzedExpr::App(fun, arg) => {
                let fun_needs_paren = matches!(fun.as_ref(), AnalyzedExpr::Abs(..));
                let arg_needs_paren = matches!(arg.as_ref(), AnalyzedExpr::App(..));
                if fun_needs_paren && arg_needs_paren {
                    write!(f, "({}) ({})", fun, arg)
                } else if fun_needs_paren {
                    write!(f, "({}) {}", fun, arg)
                } else if arg_needs_paren {
                    write!(f, "{} ({})", fun, arg)
                } else {
                    write!(f, "{} {}", fun, arg)
                }
            }
        }
    }
}

impl AnalyzedExpr {
    fn is_value(&self) -> bool {
        match self {
            AnalyzedExpr::Abs(_, _) | AnalyzedExpr::Free(_) => true,
            AnalyzedExpr::App(func, arg) => matches!(func.as_ref(), AnalyzedExpr::Free(_)) && arg.is_value(),
            _ => false
        }
    }

    /// Shift (in-place): modify self by shifting bound indices by d for indices >= cutoff
    fn shift(&mut self, d: isize, cutoff: usize) {
        match self {
            AnalyzedExpr::Free(_) => {}
            AnalyzedExpr::Bound(_, k) => {
                if *k >= cutoff {
                    let nk_signed = (*k as isize) + d;
                    if nk_signed < 0 {
                        panic!("shift produced negative index");
                    }
                    *k = nk_signed as usize;
                }
            }
            AnalyzedExpr::Abs(_, body) => body.shift(d, cutoff + 1),
            AnalyzedExpr::App(f, a) => {
                f.shift(d, cutoff);
                a.shift(d, cutoff);
            }
        }
    }

    // In-place substitute: replace occurrences of bound index j+cutoff with clonings of `s` shifted by cutoff
    fn subst(&mut self, j: usize, s: &AnalyzedExpr, cutoff: usize) {
        match self {
            AnalyzedExpr::Free(_) => {}
            AnalyzedExpr::Bound(_, k) => {
                if *k == j + cutoff {
                    // replace with s shifted by cutoff
                    let mut repl = s.clone();
                    repl.shift(cutoff as isize, 0);
                    *self = repl;
                }
            }
            AnalyzedExpr::Abs(_, body) => body.subst(j, s, cutoff + 1),
            AnalyzedExpr::App(f, a) => {
                f.subst(j, s, cutoff);
                a.subst(j, s, cutoff);
            }
        }
    }

    // substitute at top (in-place): replace index 0 in body with val
    // Performs: v1 = val shifted by +1; subst 0 with v1 in-place; then shift result by -1
    fn substitute_top(&mut self, val: &AnalyzedExpr) {
        let mut v1 = val.clone();
        v1.shift(1, 0);
        self.subst(0, &v1, 0);
        self.shift(-1, 0);
    }

    /// Substitute free variable occurrences of `name` with `val` in-place.
    /// This respects surrounding binders by shifting `val` by the current `cutoff` depth
    /// before inserting it, to maintain correct de Bruijn indices.
    fn substitute_free_inner(&mut self, name: &str, val: &AnalyzedExpr, cutoff: usize) {
        match self {
            AnalyzedExpr::Free(n) => {
                if n.as_ref() == name {
                    let mut repl = val.clone();
                    // shift cloned value by the current binder depth
                    repl.shift(cutoff as isize, 0);
                    *self = repl;
                }
            }
            AnalyzedExpr::Bound(_, _) => {}
            AnalyzedExpr::Abs(_, body) => body.substitute_free_inner(name, val, cutoff + 1),
            AnalyzedExpr::App(f, a) => {
                f.substitute_free_inner(name, val, cutoff);
                a.substitute_free_inner(name, val, cutoff);
            }
        }
    }

    /// Public wrapper: substitute free variable `name` throughout `self` with `val`.
    pub fn substitute_free(&mut self, name: &str, val: &AnalyzedExpr) {
        self.substitute_free_inner(name, val, 0);
    }

    // In-place single-step reduction following left-to-right CBV, minimizing cloning.
    fn reduce_step(&mut self) -> bool {
        match self {
            AnalyzedExpr::App(f, a) => {
                // 1) try to reduce function position in-place
                if !f.is_value() {
                    if f.reduce_step() { return true; }
                    return false;
                }
                // 2) try to reduce argument in-place
                if !a.is_value() {
                    if a.reduce_step() { return true; }
                    return false;
                }
                // 3) if function is Abs and argument is value, perform beta: replace self
                if let AnalyzedExpr::Abs(_, body) = f.as_mut() {
                    // move body and arg out to avoid cloning by replacing with a temporary Free marker
                    let mut body_owned = std::mem::take(body);
                    let arg_owned = std::mem::take(a);
                    // perform substitute_top on owned body with owned arg (in-place), then take it
                    body_owned.substitute_top(&arg_owned);
                    *self = *body_owned;
                    return true;
                }
                false
            }
            AnalyzedExpr::Abs(_, body) => {
                // reduce inside abstraction
                body.reduce_step()
            }
            AnalyzedExpr::Free(_) | AnalyzedExpr::Bound(_, _) => false,
        }
    }

    pub fn reduce(&mut self) {
        while self.reduce_step() {}
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
            // Debug prints Bound(name, #N)
            self.expect_str("#")?;
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

        Err(format!("unexpected token at {}", self.pos))
    }
}

impl std::str::FromStr for AnalyzedExpr {
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

    #[test]
    fn display_var() {
        let e = Expr::Var(Rc::new("x".to_string()));
        assert_eq!(e.to_string(), "x");
    }

    #[test]
    fn display_abs_app() {
        let body = Expr::App(Box::new(Expr::Var(Rc::new("x".into()))), Box::new(Expr::Var(Rc::new("y".into()))));
        let lam = Expr::Abs(Rc::new("z".into()), Box::new(body));
        assert_eq!(lam.to_string(), "λz.x y");
    }

    #[test]
    fn display_nested_abs() {
        // λx.λy.x y
        let inner = Expr::App(Box::new(Expr::Var(Rc::new("x".into()))), Box::new(Expr::Var(Rc::new("y".into()))));
        let lam_y = Expr::Abs(Rc::new("y".into()), Box::new(inner));
        let lam_x = Expr::Abs(Rc::new("x".into()), Box::new(lam_y));
        assert_eq!(lam_x.to_string(), "λx.λy.x y");
    }

    #[test]
    fn display_app_fun_is_abs() {
        // (λx.x) y
        let fun = Expr::Abs(Rc::new("x".into()), Box::new(Expr::Var(Rc::new("x".into()))));
        let e = Expr::App(Box::new(fun), Box::new(Expr::Var(Rc::new("y".into()))));
        assert_eq!(e.to_string(), "(λx.x) y");
    }

    #[test]
    fn display_app_arg_is_app() {
        // a (b c)
        let arg = Expr::App(Box::new(Expr::Var(Rc::new("b".into()))), Box::new(Expr::Var(Rc::new("c".into()))));
        let e = Expr::App(Box::new(Expr::Var(Rc::new("a".into()))), Box::new(arg));
        assert_eq!(e.to_string(), "a (b c)");
    }

    #[test]
    fn display_app_fun_abs_and_arg_app() {
        // (λx.x) (a b)
        let fun = Expr::Abs(Rc::new("x".into()), Box::new(Expr::Var(Rc::new("x".into()))));
        let arg = Expr::App(Box::new(Expr::Var(Rc::new("a".into()))), Box::new(Expr::Var(Rc::new("b".into()))));
        let e = Expr::App(Box::new(fun), Box::new(arg));
        assert_eq!(e.to_string(), "(λx.x) (a b)");
    }

    #[test]
    fn beta_reduce_identity() {
        // (λx.x) y -> y
        let fun = Expr::Abs(Rc::new("x".into()), Box::new(Expr::Var(Rc::new("x".into()))));
        let expr = Expr::App(Box::new(fun), Box::new(Expr::Var(Rc::new("y".into()))));
        let mut a = expr.analyze();
        a.reduce();
    let want = AnalyzedExpr::Free(Rc::new("y".into()));
    assert_eq!(a, want);
    }

    #[test]
    fn beta_reduce_nested() {
        // ((λx.λy.x) a) b -> a
        let inner = Expr::Abs(Rc::new("y".into()), Box::new(Expr::Var(Rc::new("x".into()))));
        let outer = Expr::Abs(Rc::new("x".into()), Box::new(inner));
        let app1 = Expr::App(Box::new(outer), Box::new(Expr::Var(Rc::new("a".into()))));
        let app2 = Expr::App(Box::new(app1), Box::new(Expr::Var(Rc::new("b".into()))));
        let mut a = app2.analyze();
        a.reduce();
        let want = AnalyzedExpr::Free(Rc::new("a".into()));
        assert_eq!(a, want);
    }

    #[test]
    fn call_by_value() {
        // id (id (λz.id z)) -> λz.id z
        let id = Expr::Abs(Rc::new("x".into()), Box::new(Expr::Var(Rc::new("x".into()))));
        let expr = Expr::App(Box::new(id.clone()), Box::new(Expr::App(Box::new(id.clone()), Box::new(Expr::Abs(Rc::new("z".into()), Box::new(Expr::App(Box::new(id.clone()), Box::new(Expr::Var(Rc::new("z".into()))))))))));
        let mut a = expr.analyze();
        a.reduce();
        let want = AnalyzedExpr::Abs(
            Rc::new("z".into()),
            Box::new(AnalyzedExpr::App(
                Box::new(AnalyzedExpr::Abs(Rc::new("x".into()), Box::new(AnalyzedExpr::Bound(Rc::new("x".into()), 0)))),
                Box::new(AnalyzedExpr::Bound(Rc::new("z".into()), 0)),
            )),
        );
        assert_eq!(a, want);
    }

    #[test]
    fn analyze_free_bound() {
        // λx. x y -> Abs with Bound(x,#0) and Free(y)
        let body = Expr::App(Box::new(Expr::Var(Rc::new("x".into()))), Box::new(Expr::Var(Rc::new("y".into()))));
        let lam = Expr::Abs(Rc::new("x".into()), Box::new(body));
        let a = lam.analyze();
        let want = AnalyzedExpr::Abs(Rc::new("x".into()), Box::new(AnalyzedExpr::App(Box::new(AnalyzedExpr::Bound(Rc::new("x".into()), 0)), Box::new(AnalyzedExpr::Free(Rc::new("y".into()))))));
        assert_eq!(a, want);
    }

    #[test]
    fn analyze_nested_indices() {
        // λx.λy. x y -> Bound indices 1 and 0
        let inner = Expr::App(Box::new(Expr::Var(Rc::new("x".into()))), Box::new(Expr::Var(Rc::new("y".into()))));
        let lam_y = Expr::Abs(Rc::new("y".into()), Box::new(inner));
        let lam_x = Expr::Abs(Rc::new("x".into()), Box::new(lam_y));
        let a = lam_x.analyze();
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
