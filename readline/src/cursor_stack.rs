use std::sync::Mutex;
use crossterm::{cursor, execute};
use std::io;

static CURSOR_STACK: Mutex<Vec<(u16, u16)>> = Mutex::new(Vec::new());

pub fn push_cursor() -> io::Result<()> {  
    CURSOR_STACK.lock().unwrap().push(cursor::position()?);
    Ok(())
}

pub fn pop_cursor() -> io::Result<()> {
    let position = CURSOR_STACK.lock().unwrap().pop().unwrap();
    execute!(io::stdout(), cursor::MoveTo(position.0, position.1))?;
    Ok(())
}