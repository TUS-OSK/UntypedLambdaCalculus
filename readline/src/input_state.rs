use std::io;
use arboard::Clipboard;
use crossterm::event::KeyModifiers;
use crate::input_operation::InputOperation;

/// Represents a text selection with ordered indices
#[derive(Clone, Copy, Debug)]
pub struct Selection {
    /// The anchor point where selection started
    anchor: usize,
    /// The current cursor position
    cursor: usize,
}

impl Selection {
    /// Creates a new selection starting at the given position
    pub fn new(pos: usize) -> Self {
        Self {
            anchor: pos,
            cursor: pos,
        }
    }

    /// Returns the start and end indices of the selection in ascending order
    pub fn range(&self) -> (usize, usize) {
        if self.anchor <= self.cursor {
            (self.anchor, self.cursor)
        } else {
            (self.cursor, self.anchor)
        }
    }

    /// Moves the cursor end of the selection
    pub fn set_cursor(&mut self, pos: usize) {
        self.cursor = pos;
    }
}

/// Manages the state of readline input
pub struct ReadlineState<'a> {
    /// The current input buffer as character array
    pub buffer: Vec<char>,
    /// Current cursor position (in characters)
    pub cursor_pos: usize,
    /// Current text selection, if any
    pub selection: Option<Selection>,
    /// System clipboard
    clipboard: Clipboard,
    // Current input, available if in history mode
    pub current_input: Option<String>,
    /// Command history
    pub history: &'a Vec<String>,
    /// Current position in history (-1 means not in history mode)
    pub history_pos: isize,
}

impl<'a> ReadlineState<'a> {
    pub fn new(history: &'a Vec<String>) -> io::Result<Self> {
        Ok(Self {
            buffer: Vec::new(),
            cursor_pos: 0,
            selection: None,
            clipboard: Clipboard::new().map_err(|e| io::Error::new(io::ErrorKind::Other, e))?,
            current_input: None,
            history: history,
            history_pos: -1,
        })
    }

    pub fn as_str(&self) -> String {
        self.buffer.iter().collect()
    }

    pub fn slice_str(&self, start: usize, end: usize) -> String {
        self.buffer[start..end].iter().collect()
    }

    pub fn insert(&mut self, s: &str) -> Vec<InputOperation> {
        let chars: Vec<char> = s.chars().collect();
        let chars_len = chars.len();
        if let Some(sel) = self.selection.take() {
            // Replace selection with string
            let (start, end) = sel.range();
            vec![
                InputOperation::Replace { start, end, text: chars },
                InputOperation::MoveCursor {
                    pos: start + chars_len,
                }
            ]
        } else {
            // Normal insert
            vec![
                InputOperation::Insert {
                    pos: self.cursor_pos,
                    text: chars,
                },
                InputOperation::MoveCursor {
                    pos: self.cursor_pos + chars_len,
                }
            ]
        }
    }

    pub fn backspace(&mut self) -> Vec<InputOperation> {
        if let Some(sel) = self.selection.take() {
            // Remove selection
            let (start, end) = sel.range();
            vec![
                InputOperation::Delete {
                    start,
                    end,
                },
                InputOperation::MoveCursor {
                    pos: start,
                }
            ]
        } else if self.cursor_pos > 0 {
            // Normal backspace
            vec![
                InputOperation::Delete {
                    start: self.cursor_pos - 1,
                    end: self.cursor_pos,
                },
                InputOperation::MoveCursor {
                    pos: self.cursor_pos - 1,
                }
            ]
        } else {
            vec![]
        }
    }

    pub fn delete(&mut self) -> Vec<InputOperation> {
        if let Some(sel) = self.selection.take() {
            // Remove selection
            let (start, end) = sel.range();
            vec![
                InputOperation::Delete {
                    start,
                    end,
                },
                InputOperation::MoveCursor {
                    pos: start,
                }
            ]
        } else if self.cursor_pos < self.buffer.len() {
            // Normal delete
            vec![
                InputOperation::Delete {
                    start: self.cursor_pos,
                    end: self.cursor_pos + 1,
                },
                InputOperation::MoveCursor {
                    pos: self.cursor_pos,
                }
            ]
        } else {
            vec![]
        }
    }

    pub fn get_selected_text(&self) -> Option<String> {
        self.selection.map(|sel| {
            let (start, end) = sel.range();
            self.slice_str(start, end)
        })
    }

    pub fn copy_selection(&mut self) -> io::Result<bool> {
        if let Some(text) = self.get_selected_text() {
            self.clipboard.set_text(text).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn cut_selection(&mut self) -> io::Result<Vec<InputOperation>> {
        if let Some(sel) = self.selection.take() {
            let (start, end) = sel.range();
            let text = self.slice_str(start, end);
            self.clipboard.set_text(text).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
            Ok(vec![
                InputOperation::Delete { start, end },
                InputOperation::MoveCursor { pos: start }
            ])
        } else {
            Ok(vec![])
        }
    }

    pub fn paste(&mut self) -> Vec<InputOperation> {
        if let Ok(text) = self.clipboard.get_text() && !text.is_empty() {
            self.insert(&text)
        } else {
            vec![]
        }
    }

    /// Moves the cursor with optional shift selection.
    /// Returns true if the cursor was moved.
    pub fn move_cursor(&mut self, new_pos: usize, modifiers: KeyModifiers) -> Vec<InputOperation> {
        if new_pos == self.cursor_pos {
            return vec![];
        }

        let old_pos = self.cursor_pos;

        if modifiers.contains(KeyModifiers::SHIFT) {
            let old_selection = self.selection;
            
            if let Some(sel) = &mut self.selection {
                sel.set_cursor(new_pos);
            } else {
                let mut new_sel = Selection::new(self.cursor_pos);
                new_sel.set_cursor(new_pos);
                self.selection = Some(new_sel);
            }

            vec![
                InputOperation::SelectionChanged {
                    old_selection,
                    new_selection: self.selection,
                },
                InputOperation::MoveCursor {
                    pos: new_pos,
                }
            ]
        } else {
            let had_selection = self.selection.is_some();
            self.selection = None;
            if had_selection {
                let mut old_sel = Selection::new(old_pos);
                old_sel.set_cursor(old_pos);
                vec![
                    InputOperation::SelectionChanged {
                        old_selection: Some(old_sel),
                        new_selection: None,
                    },
                    InputOperation::MoveCursor {
                        pos: new_pos,
                    }
                ]
            } else {
                vec![InputOperation::MoveCursor { pos: new_pos }]
            }
        }
    }

    pub fn move_cursor_left(&mut self, modifiers: KeyModifiers) -> Vec<InputOperation> {
        // Normal left movement
        if self.cursor_pos > 0 {
            let new_pos= if modifiers.contains(KeyModifiers::CONTROL) {
                self.find_previous_word_boundary()
            } else {
                self.cursor_pos - 1
            };
            if new_pos != self.cursor_pos {
                return self.move_cursor(new_pos, modifiers)
            }
        }
        vec![]
    }

    pub fn move_cursor_right(&mut self, modifiers: KeyModifiers) -> Vec<InputOperation> {
        if self.cursor_pos < self.buffer.len() {
            let new_pos= if modifiers.contains(KeyModifiers::CONTROL) {
                self.find_next_word_boundary()
            } else {
                self.cursor_pos + 1
            };
            if new_pos != self.cursor_pos {
                return self.move_cursor(new_pos, modifiers)
            }
        }
        vec![]
    }

    pub fn move_cursor_home(&mut self, modifiers: KeyModifiers) -> Vec<InputOperation> {
        if self.cursor_pos > 0 {
            self.move_cursor(0, modifiers)
        } else {
            vec![]
        }
    }

    pub fn move_cursor_end(&mut self, modifiers: KeyModifiers) -> Vec<InputOperation> {
        let end = self.buffer.len();
        if self.cursor_pos < end {
            self.move_cursor(end, modifiers)
        } else {
            vec![]
        }
    }

    /// Find the previous word boundary (space or start of line)
    fn find_previous_word_boundary(&self) -> usize {
        let mut pos = self.cursor_pos;
        
        // Skip any spaces at current position
        while pos > 0 && self.buffer[pos - 1] == ' ' {
            pos -= 1;
        }
        
        // Find the previous space or go to start of line
        while pos > 0 && self.buffer[pos - 1] != ' ' {
            pos -= 1;
        }
        
        pos
    }

    /// Find the next word boundary (space or end of line)
    fn find_next_word_boundary(&self) -> usize {
        let mut pos = self.cursor_pos;
        
        // Skip any spaces at current position
        while pos < self.buffer.len() && self.buffer[pos] == ' ' {
            pos += 1;
        }
        
        // Find the next space or go to end of line
        while pos < self.buffer.len() && self.buffer[pos] != ' ' {
            pos += 1;
        }
        
        pos
    }
}
