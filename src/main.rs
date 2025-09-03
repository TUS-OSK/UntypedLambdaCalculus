mod greek;
mod commands;
mod token;
mod lexer;
mod ast;
mod parser;

use std::io;
use std::rc::Rc;

use ariadne::Source;

use ast::Stmt;

use crate::ast::AnalyzedExpr;

fn main() -> io::Result<()> {
    let mut history = Vec::new();
    let mut variables = Vec::new();

    // completer that knows about slash-commands and delegates to GreekCompleter
    let completer = commands::CommandCompleter::new();

    loop {
        let input = match readline::read_line_with_completion(&completer, &history) {
            Ok(line) => line,
            Err(e) => return Err(io::Error::new(io::ErrorKind::Other, e)),
        };

        let trimmed = input.trim();

        if trimmed.is_empty() {
            continue;
        }

        // slash-commands handled separately
        if trimmed.starts_with('/') {
            let should_quit = commands::handle_command(trimmed, &mut variables)?;
            if should_quit {
                break;
            }
            history.push(input);
            continue;
        }

        handle_input(&input, &mut variables)?;
        history.push(input);
    }
    Ok(())
}

fn evaluate(mut expr: AnalyzedExpr, variables: &Vec<(Rc<String>, AnalyzedExpr)>) -> AnalyzedExpr {
    for (name, value) in variables.iter().rev() {
        expr.substitute_free(name, value);
    }
    expr.reduce();
    expr
}

fn handle_input(input: &str, variables: &mut Vec<(Rc<String>, AnalyzedExpr)>) -> io::Result<()> {
    match parser::parse(input) {
        Ok(Stmt::Expr(expr)) => {
            let analyzed = expr.analyze();
            let reduced = evaluate(analyzed, &variables);
            println!("{} -> {}", expr, reduced);
        }
        Ok(Stmt::Def(name, expr)) => {
            let analyzed = expr.analyze();
            println!("{} = {}", name, analyzed);
            variables.push((name, analyzed));
        }
        Err(e) => {
            e.report().print(Source::from(input.to_string()))?;
        }
    }
    Ok(())
}