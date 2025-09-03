use readline::{Completion, CompletionEntry, Completer};

/// Unified Greek letter processing module
/// Contains all Greek letter data and operations in one place

/// Raw Greek letter mappings - the single source of truth
const GREEK_LETTERS: &[(&str, char)] = &[
    // Lowercase Greek letters
    ("\\alpha", 'α'), ("\\beta", 'β'), ("\\gamma", 'γ'), ("\\delta", 'δ'),
    ("\\epsilon", 'ε'), ("\\zeta", 'ζ'), ("\\eta", 'η'), ("\\theta", 'θ'),
    ("\\iota", 'ι'), ("\\kappa", 'κ'), ("\\lambda", 'λ'), ("\\mu", 'μ'),
    ("\\nu", 'ν'), ("\\xi", 'ξ'), ("\\omicron", 'ο'), ("\\pi", 'π'),
    ("\\rho", 'ρ'), ("\\sigma", 'σ'), ("\\tau", 'τ'), ("\\upsilon", 'υ'),
    ("\\phi", 'φ'), ("\\chi", 'χ'), ("\\psi", 'ψ'), ("\\omega", 'ω'),

    // Uppercase Greek letters
    ("\\Alpha", 'Α'), ("\\Beta", 'Β'), ("\\Gamma", 'Γ'), ("\\Delta", 'Δ'),
    ("\\Epsilon", 'Ε'), ("\\Zeta", 'Ζ'), ("\\Eta", 'Η'), ("\\Theta", 'Θ'),
    ("\\Iota", 'Ι'), ("\\Kappa", 'Κ'), ("\\Lambda", 'Λ'), ("\\Mu", 'Μ'),
    ("\\Nu", 'Ν'), ("\\Xi", 'Ξ'), ("\\Omicron", 'Ο'), ("\\Pi", 'Π'),
    ("\\Rho", 'Ρ'), ("\\Sigma", 'Σ'), ("\\Tau", 'Τ'), ("\\Upsilon", 'Υ'),
    ("\\Phi", 'Φ'), ("\\Chi", 'Χ'), ("\\Psi", 'Ψ'), ("\\Omega", 'Ω')
];

/// Find all patterns that start with the given prefix for completion
fn find_completions(prefix: &str) -> Vec<CompletionEntry> {
    GREEK_LETTERS
        .iter()
        .filter(|(pattern, _)| pattern.starts_with(prefix))
        .map(|(pattern, char)| CompletionEntry { text: vec![*char], from: Some(pattern.chars().collect()) })
        .collect()
}

fn find_backslash_prefix(input: &Vec<char>, cursor_pos: usize) -> Option<usize> {
    if cursor_pos == 0 {
        None
    } else {
        input[..cursor_pos].iter().rposition(|c| *c == '\\')
    }
}

pub struct GreekCompleter;

impl Completer for GreekCompleter {
    fn complete(&self, input: &Vec<char>, cursor_pos: usize) -> Option<Completion> {
        if let Some(start) = find_backslash_prefix(input, cursor_pos) {
            let prefix = input[start..cursor_pos].iter().collect::<String>();
            let completions = find_completions(&prefix);
            if completions.is_empty() {
                None
            } else {
                Some(Completion { start, len: prefix.chars().count(), options: completions })
            }
        } else {
            None
        }
    }
}