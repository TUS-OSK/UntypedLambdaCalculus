pub struct Completion {
    pub start: usize,
    pub len: usize,
    pub options: Vec<CompletionEntry>,
}

pub struct CompletionEntry {
    pub text: Vec<char>,
    pub from: Option<Vec<char>>
}

impl CompletionEntry {
    pub fn display(&self) -> Vec<char> {
        match &self.from {
            Some(from) => format!(
                "{} -> {}",
                from.iter().collect::<String>(),
                self.text.iter().collect::<String>()
            ),
            None => self.text.iter().collect::<String>(),
        }.chars().collect()
    }
}

pub trait Completer {
    fn complete(&self, input: &Vec<char>, cursor_pos: usize) -> Option<Completion>;
}