use crate::ast::AnalyzedExpr;
use std::io;
use std::fs;
use std::rc::Rc;
use readline::{Completion, CompletionEntry, Completer};

/// Supported commands
const COMMANDS: &[&str] = &["/quit", "/export", "/import", "/clear", "/variables"];

/// Handle a slash-command. Returns Ok(true) if the REPL should quit.
pub fn handle_command(line: &str, variables: &mut Vec<(Rc<String>, AnalyzedExpr)>) -> io::Result<bool> {
    let mut parts = line.split_whitespace();
    let cmd = parts.next().unwrap_or("");
    match cmd {
        "/quit" => Ok(true),
        "/clear" => {
            variables.clear();
            println!("cleared variables");
            Ok(false)
        }
        "/variables" => {
            list_variables(variables);
            Ok(false)
        }
        "/export" => {
            // allow paths with spaces: take the rest of the line after the command
            let rest = line[cmd.len()..].trim();
            let unquote = |s: &str| -> String {
                let t = s.trim();
                if t.len() >= 2 && ((t.starts_with('"') && t.ends_with('"')) || (t.starts_with('\'') && t.ends_with('\''))) {
                    t[1..t.len()-1].to_string()
                } else { t.to_string() }
            };
            let path_buf = if rest.is_empty() { "lambda_vars.txt".to_string() } else { unquote(rest) };
            match export_variables(&path_buf, variables) {
                Ok(b) => Ok(b),
                Err(e) => { println!("export error: {}", e); Ok(false) }
            }
        }
        "/import" => {
            // allow paths with spaces: take the rest of the line after the command
            let rest = line[cmd.len()..].trim();
            if rest.is_empty() {
                println!("missing filename for /import");
                Ok(false)
            } else {
                let unquote = |s: &str| -> String {
                    let t = s.trim();
                    if t.len() >= 2 && ((t.starts_with('"') && t.ends_with('"')) || (t.starts_with('\'') && t.ends_with('\''))) {
                        t[1..t.len()-1].to_string()
                    } else { t.to_string() }
                };
                let path_buf = unquote(rest);
                match import_variables(&path_buf, variables) {
                    Ok(b) => Ok(b),
                    Err(e) => { println!("import error: {}", e); Ok(false) }
                }
            }
        }
        _ => {
            println!("unknown command: {}", cmd);
            Ok(false)
        }
    }
}

fn export_variables(path: &str, variables: &Vec<(Rc<String>, AnalyzedExpr)>) -> io::Result<bool> {
    let mut out = String::new();
    for (name, expr) in variables.iter() {
        out.push_str(&format!("{} = {:?}\n", name.as_str(), expr));
    }
    match fs::write(path, out) {
        Ok(()) => {
            println!("exported {} variables to {}", variables.len(), path);
            Ok(false)
        }
        Err(e) => {
            println!("failed to export to {}: {}", path, e);
            Err(e)
        }
    }
}

fn import_variables(path: &str, variables: &mut Vec<(Rc<String>, AnalyzedExpr)>) -> io::Result<bool> {
    let s = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => return Err(e),
    };
    let before = variables.len();
    for (i, raw_line) in s.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() { continue; }

        // expected format: name = <Debug output of AnalyzedExpr>
        if let Some(eq_pos) = line.find('=') {
            let left = line[..eq_pos].trim();
            let right = line[eq_pos+1..].trim();
            if left.is_empty() {
                println!("skipping line {}: empty name", i+1);
                continue;
            }
            match right.parse::<AnalyzedExpr>() {
                Ok(expr) => {
                    variables.push((Rc::new(left.to_string()), expr));
                }
                Err(e) => {
                    println!("skipping line {}: failed to parse AnalyzedExpr: {}", i+1, e);
                    continue;
                }
            }
        } else {
            println!("skipping line {}: expected `name = <expr>`", i+1);
            continue;
        }
    }
    let added = variables.len().saturating_sub(before);
    if added == 0 {
        println!("no variables imported from {}", path);
    } else {
        println!("imported {} variables from {}", added, path);
    }
    Ok(false)
}

fn list_variables(variables: &Vec<(Rc<String>, AnalyzedExpr)>) {
    if variables.is_empty() {
        println!("no variables defined");
        return;
    }
    for (name, expr) in variables.iter() {
        println!("{} = {}", name, expr);
    }
    println!("(total: {} variable(s))", variables.len());
}

/// Completer that offers slash-commands when input begins with '/'
pub struct CommandCompleter {
    greek: crate::greek::GreekCompleter,
}

impl CommandCompleter {
    pub fn new() -> Self {
        Self { greek: crate::greek::GreekCompleter }
    }
}

impl Completer for CommandCompleter {
    fn complete(&self, input: &Vec<char>, cursor_pos: usize) -> Option<Completion> {
        // if the input starts with '/', offer commands
        if !input.is_empty() && input[0] == '/' {
            // find the prefix up to cursor_pos
            let prefix = input[..cursor_pos].iter().collect::<String>();

            // Special-case: '/import ' followed by a filename prefix -> offer file names
            if prefix.starts_with("/import ") {
                use std::path::Path;
                // compute start and prefix using the original input Vec<char>
                // find the index of the first char of the filename portion in the input
                // locate the position after the literal "/import " in chars
                let import_len = "/import ".chars().count();
                // compute dir_part/name_prefix using the raw input vector up to cursor_pos
                let after_chars: String = input[import_len..cursor_pos].iter().collect();
                let after = after_chars.as_str();

                let last_sep = after.rmatch_indices('/').next().map(|(i,_)| i)
                    .or_else(|| after.rmatch_indices('\\').next().map(|(i,_)| i));

                let (dir_part, name_prefix) = match last_sep {
                    Some(idx) => (&after[..=idx], &after[idx+1..]),
                    None => ("", after),
                };

                // start at the first character of the file path (after `/import `)
                let start = import_len;
                let replace_len = cursor_pos.saturating_sub(import_len);

                let dir_path = if dir_part.is_empty() { Path::new(".") } else { Path::new(dir_part) };
                let mut matches: Vec<CompletionEntry> = Vec::new();
                if let Ok(rd) = std::fs::read_dir(dir_path) {
                    for entry in rd.filter_map(Result::ok) {
                        // convert file name to String if possible
                        if let Ok(name_os) = entry.file_name().into_string() {
                            if name_os.starts_with(name_prefix) {
                                // build suggestion: full path (dir_part + name), append separator for directories
                                let mut suggestion = String::new();
                                suggestion.push_str(dir_part);
                                suggestion.push_str(&name_os);
                                let is_dir = entry.file_type().map(|ft| ft.is_dir()).unwrap_or(false);
                                if is_dir {
                                    let sep = if dir_part.contains('/') { '/' } else { std::path::MAIN_SEPARATOR };
                                    suggestion.push(sep);
                                }
                                matches.push(CompletionEntry { text: suggestion.chars().collect(), from: None });
                            }
                        }
                    }
                }
                if matches.is_empty() { None } else { Some(Completion { start, len: replace_len, options: matches }) }
            } else {
                let matches: Vec<CompletionEntry> = COMMANDS.iter()
                    .filter(|c| c.starts_with(&prefix))
                    .map(|c| CompletionEntry { text: c.chars().collect(), from: None })
                    .collect();
                if matches.is_empty() {
                    None
                } else {
                    Some(Completion { start: 0, len: prefix.chars().count(), options: matches })
                }
            }
        } else {
            // delegate to greek completer
            self.greek.complete(input, cursor_pos)
        }
    }
}
