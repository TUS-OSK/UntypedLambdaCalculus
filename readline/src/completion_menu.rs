use std::io::{self, Write};
use crossterm::{
    cursor::{MoveDown, MoveToColumn, MoveUp},
    execute,
    style::{Color, Print, ResetColor, SetBackgroundColor},
    terminal
};

use crate::{completion::CompletionEntry, cursor_stack};
/// Manages the state of tab completion functionality
pub struct CompletionHandler {
    /// Whether completion mode is active
    active: bool,
    /// Available completion options
    pub options: Vec<CompletionEntry>,
    /// Current index in completion options
    pub current_index: usize,
    /// Start position of the prefix being completed
    pub start: usize,
    last_dropdown_height: usize,
    pub dropdown_height: usize,
    pub dropdown_offset: usize
}

impl CompletionHandler {
    pub fn new() -> Self {
        Self {
            active: false,
            options: Vec::new(),
            current_index: 0,
            start: 0,
            last_dropdown_height: 0,
            dropdown_height: 0,
            dropdown_offset: 0,
        }
    }

    pub fn enter_mode(&mut self, start: usize, options: Vec<CompletionEntry>) -> io::Result<()> {
        self.active = true;
        self.current_index = 0;
        self.start = start;
        self.options = options;
        self.last_dropdown_height = 0;
        self.dropdown_height = self.options.len().min(terminal::size()?.1 as usize - 1);
        self.dropdown_offset = 0;
        Ok(())
    }

    pub fn exit_mode(&mut self) -> io::Result<()> {
        self.active = false;
        let mut stdout = io::stdout();
        // Save cursor position
        cursor_stack::push_cursor()?;
         
        // Clear all menu lines
        for _ in 0..self.dropdown_height {
            execute!(stdout, MoveDown(1), Print("\r\x1B[K"))?;
        }
         
        // Move back to original position
        cursor_stack::pop_cursor()?;
        
        execute!(stdout, MoveToColumn(2 + self.start as u16 + self.options[self.current_index].text.len() as u16))?;
        stdout.flush()?;
        self.options.clear();
        Ok(())
    }

    pub fn cycle_next(&mut self) -> io::Result<()> {
        if !self.options.is_empty() {
            self.current_index = (self.current_index + 1) % self.options.len();
            self.update_dropdown()?;
        }
        Ok(())
    }

    pub fn cycle_prev(&mut self) -> io::Result<()> {
        if !self.options.is_empty() {
            if self.current_index > 0 {
                self.current_index -= 1;
            } else {
                self.current_index = self.options.len() - 1;
            }
            self.update_dropdown()?;
        }
        Ok(())
    }

    pub fn current_option(&self) -> &CompletionEntry {
        &self.options[self.current_index]
    }

    pub fn is_active(&self) -> bool {
        self.active
    }

    pub fn draw_completion_menu(&mut self) -> io::Result<()> {
        let mut stdout = io::stdout();
        clear_lines_below(self.last_dropdown_height)?;
        let lengths = (self.dropdown_offset..self.dropdown_offset + self.dropdown_height)
            .clone()
            .map(|i| self.options[i].display().len())
            .collect::<Vec<_>>();
        let max_len = *lengths.iter().max().unwrap_or(&0);
        for i in 0..self.dropdown_height {
            let index = self.dropdown_offset + i;
            execute!(stdout, Print("\r\n"))?;
            let option = &self.options[index];
            if index == self.current_index {
                execute!(
                    stdout,
                    SetBackgroundColor(Color::DarkCyan),
                    Print("  "),
                    Print(option.display().iter().collect::<String>()),
                    Print(" ".repeat(max_len - lengths[i] + 1)),
                    ResetColor
                )?;
            } else {
                execute!(
                    stdout,
                    Print("  "),
                    Print(option.display().iter().collect::<String>()),
                    Print(" ".repeat(max_len - lengths[i] + 1))
                )?;
            }
        }
        execute!(stdout, MoveToColumn(2 + self.start as u16), MoveUp(self.dropdown_height as u16))?;
        stdout.flush()?;
        Ok(())
    }

    fn update_dropdown(&mut self) -> io::Result<()> {
        // Clamp the number of options to the number of lines in the terminal
        self.last_dropdown_height = self.dropdown_height;
        self.dropdown_height = self.options.len().min(terminal::size()?.1 as usize - 1);
        if self.dropdown_offset + self.dropdown_height <= self.current_index {
            self.dropdown_offset = self.current_index - self.dropdown_height + 1;
        } else if self.dropdown_offset > self.current_index {
            self.dropdown_offset = self.current_index;
        }
        Ok(())
    }
}

fn clear_lines_below(count: usize) -> io::Result<()> {
    let mut stdout = io::stdout();
    cursor_stack::push_cursor()?;
    execute!(stdout, Print("\r"))?;
    for _ in 0..count {
        execute!(stdout, MoveDown(1), Print("\x1B[K"))?;
    }
    cursor_stack::pop_cursor()?;
    Ok(())
}