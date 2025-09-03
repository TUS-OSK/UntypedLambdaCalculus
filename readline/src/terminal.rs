use crossterm::{
    cursor,
    event::{self, Event, KeyCode, KeyEvent, KeyModifiers},
    execute,
    style::Print,
    terminal,
};
use std::io::{self, Write};
use std::sync::Once;

use crate::input_state::{ReadlineState, Selection};
use crate::completion::{Completion, Completer};
use crate::completion_menu::CompletionHandler;
use crate::input_operation::InputOperation;

static SET_PANIC_HOOK: Once = Once::new();

pub fn read_line_with_completion(completion_handler: &impl Completer, history: &Vec<String>) -> io::Result<String> {
    SET_PANIC_HOOK.call_once(|| {
        let default_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |panic_info| {
            let _ = terminal::disable_raw_mode();
            let mut stdout = io::stdout();
            let _ = execute!(stdout, Print("\n"));
            default_hook(panic_info);
        }));
    });
    let mut readline_state = ReadlineState::new(history)?;
    let mut completion_state = CompletionHandler::new();

    // Enable raw mode for direct terminal control
    terminal::enable_raw_mode()?;
    
    // Ensure we're using the right terminal stream
    let mut stdout = io::stdout();
    
    // Print initial prompt and ensure cursor is at the right position
    execute!(stdout, Print("> "))?;
    stdout.flush()?;
    
    loop {
        // Read a single event
        match event::read()? {
            Event::Key(KeyEvent { code, modifiers, kind: event::KeyEventKind::Press, .. }) => {
                match code {
                    KeyCode::Char(c) => {
                        exit_completion_if_active(&mut completion_state)?;
                        
                        if modifiers.contains(KeyModifiers::CONTROL) {
                            match c {
                                'a' => {
                                    // Ctrl+A - select all
                                    handle_input_modification(&mut readline_state, |state| {
                                        let mut sel = Selection::new(0);
                                        sel.set_cursor(state.buffer.len());
                                        let old_selection = state.selection.take();
                                        state.selection = Some(sel);
                                        vec![
                                            InputOperation::SelectionChanged {
                                                old_selection,
                                                new_selection: state.selection,
                                            }
                                        ]
                                    })?;
                                }
                                'c' => {
                                    // Ctrl+C - copy selection or exit if no selection
                                    if !readline_state.copy_selection()? {
                                        // No selection, exit program
                                        exit()?;
                                    }
                                }
                                'd' => {
                                    // Ctrl+D - EOF
                                    exit()?;
                                }
                                'x' => {
                                    // Ctrl+X - cut selection
                                    handle_input_modification(&mut readline_state, |state| {
                                        state.cut_selection().unwrap_or_default()
                                    })?;
                                }
                                'v' => {
                                    // Ctrl+V - paste from clipboard
                                    handle_input_modification(&mut readline_state, |state| state.paste())?;
                                }
                                _ => {}
                            }
                        } else {
                            // Insert character at cursor position
                            handle_input_modification(&mut readline_state, |state| state.insert(&c.to_string()))?;
                        }
                    }
                    KeyCode::Backspace => {
                        exit_completion_if_active(&mut completion_state)?;
                        
                        handle_input_modification(&mut readline_state, |state| state.backspace())?;
                    }
                    KeyCode::Tab => {
                        if !completion_state.is_active() {
                            // First Tab press - check for completions
                            if let Some(Completion { start, len, options }) = completion_handler.complete(&readline_state.buffer, readline_state.cursor_pos) {
                                if options.len() > 1 {
                                    // Multiple options - enter completion mode
                                    completion_state.enter_mode(start, options)?;
                                    
                                    // Apply first completion and show menu
                                    let completion = completion_state.current_option();
                                    let completion_len = completion.text.len();
                                    handle_input_modification(&mut readline_state, |_| {
                                        vec![
                                            InputOperation::Replace {
                                                start,
                                                end: start + len,
                                                text: completion.text.clone(),
                                            },
                                            InputOperation::MoveCursor {
                                                pos: start + completion_len,
                                            }
                                        ]
                                    })?;
                                    completion_state.draw_completion_menu()?;
                                } else if options.len() == 1 {
                                    apply_completion(&mut readline_state, start, len, options.into_iter().next().unwrap().text)?;
                                }
                            }
                        } else {
                            // Already in completion mode - cycle to next option
                            let prev_completion = completion_state.current_option();
                            let prev_len = prev_completion.text.len();
                            completion_state.cycle_next()?;
                            let completion = completion_state.current_option();
                            let completion_len = completion.text.len();
                            handle_input_modification(&mut readline_state, |_| {
                                vec![
                                    InputOperation::Replace {
                                        start: completion_state.start,
                                        end: completion_state.start + prev_len,
                                        text: completion.text.clone(),
                                    },
                                    InputOperation::MoveCursor {
                                        pos: completion_state.start + completion_len,
                                    }
                                ]
                            })?;
                            completion_state.draw_completion_menu()?;
                        }
                    }
                    KeyCode::Enter => {
                        if completion_state.is_active() {
                            // Just finalize completion selection
                            completion_state.exit_mode()?;
                        } else {
                            // Clear any selection
                            if readline_state.selection.is_some() {
                                handle_input_modification(&mut readline_state, |state| {
                                    let old_selection = state.selection.take();
                                    vec![InputOperation::SelectionChanged {
                                        old_selection,
                                        new_selection: None,
                                    }]
                                })?;
                            }
                            let input = readline_state.as_str();
                            terminal::disable_raw_mode()?;
                            execute!(stdout, Print("\n"))?;
                            return Ok(input);
                        }
                    }
                    KeyCode::Up | KeyCode::Down => {
                        if completion_state.is_active() {
                            // Only Up/Down arrows cycle through completions
                            let prev_completion = completion_state.current_option();
                            let prev_len = prev_completion.text.len();
                            match code {
                                KeyCode::Up => completion_state.cycle_prev()?,
                                KeyCode::Down => completion_state.cycle_next()?,
                                _ => unreachable!(),
                            }
                            let completion = completion_state.current_option();
                            let completion_len = completion.text.len();
                            handle_input_modification(&mut readline_state, |_| {
                                vec![
                                    InputOperation::Replace {
                                        start: completion_state.start,
                                        end: completion_state.start + prev_len,
                                        text: completion.text.clone(),
                                    },
                                    InputOperation::MoveCursor {
                                        pos: completion_state.start + completion_len,
                                    }
                                ]
                            })?;
                            completion_state.draw_completion_menu()?;
                        } else {
                            // Up/Down arrows navigate history outside completion mode
                            match code {
                                KeyCode::Up => {
                                    handle_input_modification(&mut readline_state, |state| {
                                        if state.history.len() > 0 {
                                            if state.history_pos == -1 {
                                                // First time pressing Up - go to most recent history entry
                                                state.history_pos = state.history.len() as isize - 1;
                                                state.current_input = Some(state.buffer.iter().collect());
                                            } else if state.history_pos > 0 {
                                                // Go to older entry
                                                state.history_pos -= 1;
                                            }
                                            let history_entry = &state.history[state.history_pos as usize];
                                            let history_chars: Vec<char> = history_entry.chars().collect();
                                            let history_len = history_chars.len();
                                            vec![
                                                InputOperation::Replace {
                                                    start: 0,
                                                    end: state.buffer.len(),
                                                    text: history_chars,
                                                },
                                                InputOperation::MoveCursor {
                                                    pos: history_len,
                                                }
                                            ]
                                        } else {
                                            vec![]
                                        }
                                    })?;
                                }
                                KeyCode::Down => {
                                    handle_input_modification(&mut readline_state, |state| {
                                        if state.history_pos >= 0 {
                                            let text: Vec<char> = if state.history_pos < (state.history.len() as isize - 1) {
                                                state.history_pos += 1;
                                                state.history[state.history_pos as usize].clone()
                                            } else {
                                                state.history_pos = -1;
                                                state.current_input.take().unwrap_or_default()
                                            }.chars().collect();
                                            let text_len = text.len();
                                            vec![
                                                InputOperation::Replace {
                                                    start: 0,
                                                    end: state.buffer.len(),
                                                    text: text,
                                                },
                                                InputOperation::MoveCursor {
                                                    pos: text_len,
                                                }
                                            ]
                                        } else {
                                            vec![]
                                        }
                                    })?;
                                }
                                _ => unreachable!()
                            }
                        }
                    }
                    KeyCode::Left | KeyCode::Right => {
                        // Normal cursor movement
                        exit_completion_if_active(&mut completion_state)?;
                        
                        match code {
                            KeyCode::Left => {
                                handle_input_modification(&mut readline_state, |state| {
                                    if !modifiers.contains(KeyModifiers::SHIFT) && let Some(old_selection) = state.selection.take() {
                                        // Jump to start of selection
                                        let pos = old_selection.range().0;
                                        vec![
                                            InputOperation::SelectionChanged {
                                                old_selection: Some(old_selection),
                                                new_selection: None,
                                            },
                                            InputOperation::MoveCursor { pos }
                                        ]
                                    } else {
                                        state.move_cursor_left(modifiers)
                                    }
                                })?;
                            }
                            KeyCode::Right => {
                                handle_input_modification(&mut readline_state, |state| {
                                    if !modifiers.contains(KeyModifiers::SHIFT) && let Some(old_selection) = state.selection.take() {
                                        // Jump to end of selection
                                        let pos = old_selection.range().1;
                                        vec![
                                            InputOperation::SelectionChanged {
                                                old_selection: Some(old_selection),
                                                new_selection: None,
                                            },
                                            InputOperation::MoveCursor { pos }
                                        ]
                                    } else {
                                        state.move_cursor_right(modifiers)
                                    }
                                })?;
                            }
                            _ => {}
                        }
                    }
                    KeyCode::Delete => {
                        exit_completion_if_active(&mut completion_state)?;
                        
                        handle_input_modification(&mut readline_state, |state| state.delete())?;
                    }
                    KeyCode::Home => {
                        exit_completion_if_active(&mut completion_state)?;
                        
                        // Move cursor to beginning of input
                        handle_input_modification(&mut readline_state, |state| state.move_cursor_home(modifiers))?;
                    }
                    KeyCode::End => {
                        exit_completion_if_active(&mut completion_state)?;
                        
                        // Move cursor to end of input
                        handle_input_modification(&mut readline_state, |state| state.move_cursor_end(modifiers))?;
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

fn exit() -> io::Result<()> {
    let mut stdout = io::stdout();
    execute!(stdout, Print("\n"))?;
    execute!(stdout, cursor::MoveToColumn(0))?;
    terminal::disable_raw_mode()?;
    std::process::exit(0);
}

fn exit_completion_if_active(completion_state: &mut CompletionHandler) -> io::Result<()> {
    if completion_state.is_active() {
        completion_state.exit_mode()?;
    }
    Ok(())
}

fn handle_input_modification(readline_state: &mut ReadlineState, modify: impl FnOnce(&mut ReadlineState) -> Vec<InputOperation>) -> io::Result<()> {
    let modifications = modify(readline_state);
    for modification in modifications {
        modification.apply_and_display(&mut readline_state.buffer, &mut readline_state.cursor_pos)?;
    }
    Ok(())
}

fn apply_completion(
    readline_state: &mut ReadlineState,
    start: usize,
    len: usize,
    completion: Vec<char>,
) -> io::Result<()> {
    let completion_len = completion.len();
    handle_input_modification(readline_state, |_| {
        vec![
            InputOperation::Replace {
                start,
                end: start + len,
                text: completion,
            },
            InputOperation::MoveCursor {
                pos: start + completion_len,
            }
        ]
    })
}