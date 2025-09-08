use std::fmt::{self, Formatter};

pub struct PrettyPrinter<'a, 'b> {
    formatter: &'a mut Formatter<'b>,
    is_first_entry: Vec<bool>,
    indent: u8,
    indent_level: usize
}

impl<'a, 'b> PrettyPrinter<'a, 'b> {

    pub fn new(formatter: &'a mut Formatter<'b>, indent: u8) -> Self {
        PrettyPrinter {
            formatter,
            is_first_entry: vec![true],
            indent,
            indent_level: 0
        }
    }

    pub fn push(&mut self, bracket: char) -> fmt::Result {
        self.is_first_entry.push(true);
        if self.formatter.alternate() {
            self.indent_level += 1;
            write!(self.formatter, "{}\n", bracket)
        } else {
            write!(self.formatter, "{}", bracket)
        }
    }

    pub fn print_entry(&mut self, s: impl AsRef<str>) -> fmt::Result {
        let alternate = self.formatter.alternate();
        if !self.is_first_entry.last().copied().unwrap() {
            write!(self.formatter, "{}", if alternate { ",\n" } else { ", " })?;
        } else {
            let len = self.is_first_entry.len();
            self.is_first_entry[len - 1] = false;
        }
        if alternate {
            let indent_str = " ".repeat(self.indent as usize * self.indent_level);
            write!(self.formatter, "{}{}", indent_str, s.as_ref())
        } else {
            write!(self.formatter, "{}", s.as_ref())
        }
    }
    
    pub fn pop(&mut self, bracket: char) -> fmt::Result {
        self.is_first_entry.pop();
        if self.formatter.alternate() {
            self.indent_level -= 1;
            let indent_str = " ".repeat(self.indent as usize * self.indent_level);
            write!(self.formatter, "\n{}{}", indent_str, bracket)
        } else {
            write!(self.formatter, "{}", bracket)
        }
    }
}