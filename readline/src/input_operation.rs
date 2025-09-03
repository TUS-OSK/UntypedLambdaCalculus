use std::io::{self, Write};
use crossterm::{
    cursor,
    execute,
    style::{Print, SetBackgroundColor, ResetColor, Color},
};
use crate::input_state::Selection;

/// Represents different types of input modifications and their display requirements
#[derive(Debug)]
pub enum InputOperation {
    /// Insert text at position (handles both single char and string)
    Insert {
        pos: usize,
        text: Vec<char>,
    },
    /// Delete range of text
    Delete {
        start: usize,
        end: usize,
    },
    /// Replace range of text with new text
    Replace {
        start: usize,
        end: usize,
        text: Vec<char>,
    },
    /// Selection changed (just visual update)
    SelectionChanged {
        old_selection: Option<Selection>,
        new_selection: Option<Selection>,
    },
    /// Move cursor to position
    MoveCursor {
        pos: usize,
    },
}

impl InputOperation {
    /// Apply the modification to the buffer and display the changes
    pub fn apply_and_display(&self, buffer: &mut Vec<char>, cursor_pos: &mut usize) -> io::Result<()> {
        let mut stdout = io::stdout();
        
        match self {
            Self::Insert { pos, text } => {
                // Move to insertion point and prepare to redraw
                execute!(stdout, cursor::MoveToColumn(2 + *pos as u16))?;
                
                // Modify buffer
                buffer.splice(*pos..*pos, text.iter().copied());
                
                // Print new text
                let text_str: String = text.iter().collect();
                execute!(stdout, Print(text_str))?;
                
                // Print rest of line if any
                if *pos + text.len() < buffer.len() {
                    let rest: String = buffer[*pos + text.len()..].iter().collect();
                    execute!(stdout, Print(rest))?;
                }
            }
            
            Self::Delete { start, end } => {
                // Move to start of deletion
                execute!(stdout, cursor::MoveToColumn(2 + *start as u16))?;
                
                // Modify buffer
                buffer.splice(*start..*end, std::iter::empty());
                
                // Print rest of line and clear remaining space
                let rest: String = buffer[*start..].iter().collect();
                execute!(stdout, Print(&rest))?;
                execute!(stdout, Print(" ".repeat(end - start)))?;
                // Move cursor back to where the rest of text starts
                execute!(stdout, cursor::MoveToColumn(2 + *start as u16))?;
                // Print the rest again to overwrite the spaces
                execute!(stdout, Print(&rest))?;
            }
            
            Self::Replace { start, end, text } => {
                // Move to start of replacement
                execute!(stdout, cursor::MoveToColumn(2 + *start as u16))?;
                
                // Modify buffer
                buffer.splice(*start..*end, text.iter().copied());
                

                // Print new text
                let text_str: String = text.iter().collect();
                execute!(stdout, Print(text_str))?;

                let diff = (*end - *start).saturating_sub(text.len());

                if diff == 0 {
                    return Ok(());
                }
                // Print the rest of the line
                let rest: String = buffer[*end - diff..].iter().collect();
                execute!(stdout, Print(&rest))?;

                if diff > 0 {
                    execute!(stdout, Print(" ".repeat(diff)))?;
                }

                execute!(stdout, cursor::MoveToColumn(2 + *start as u16))?;
            }
            
            Self::SelectionChanged { old_selection, new_selection } => {
                // Find the range that needs updating
                let old_range = old_selection.map(|s| s.range()).unwrap_or((0, 0));
                let new_range = new_selection.map(|s| s.range()).unwrap_or((0, 0));
                let start = old_range.0.min(new_range.0);
                let end = old_range.1.max(new_range.1);
                
                if start < end {
                    // Move to start of selection
                    execute!(stdout, cursor::MoveToColumn(2 + start as u16))?;
                    
                    // Print text with appropriate highlighting
                    let text: String = buffer[start..end].iter().collect();
                    if let Some(sel) = new_selection {
                        let (sel_start, sel_end) = sel.range();
                        if sel_start < sel_end {
                            // Print before selection
                            if start < sel_start {
                                let before = buffer[start..sel_start].iter().collect::<String>();
                                execute!(stdout, Print(before))?;
                            }
                            // Print selection with highlight
                            let selected = buffer[sel_start..sel_end].iter().collect::<String>();
                            execute!(stdout, SetBackgroundColor(Color::Grey), Print(selected), ResetColor)?;
                            // Print after selection
                            if sel_end < end {
                                let after = buffer[sel_end..end].iter().collect::<String>();
                                execute!(stdout, Print(after))?;
                            }
                        } else {
                            execute!(stdout, Print(text))?;
                        }
                    } else {
                        execute!(stdout, Print(text))?;
                    }
                }
            }
            
            Self::MoveCursor { pos } => {
                // Just update cursor position
                *cursor_pos = *pos;
                execute!(stdout, cursor::MoveToColumn(2 + *pos as u16))?;
            }
        }
        
        stdout.flush()?;
        Ok(())
    }
}
