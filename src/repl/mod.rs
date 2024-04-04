use crate::environment::Environment;
use crate::evaluator;
use crate::lexer;
use crate::parser;
use std::cell::RefCell;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::rc::Rc;

const PROMPT: &str = ">> ";

pub fn start<R: Read, W: Write>(reader: R, writer: &mut W) -> io::Result<()> {
    let mut reader = BufReader::new(reader);
    let env = Rc::new(RefCell::new(Environment::new()));
    loop {
        write!(writer, "{}", PROMPT)?;
        writer.flush()?;

        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            break;
        }

        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        let mut lexer = lexer::Lexer::new(line);
        let mut parser = parser::Parser::new(&mut lexer);

        if let Ok(program) = parser.parse_program() {
            match evaluator::eval(program.into(), env.clone()) {
                Ok(evaluated) => writeln!(writer, "{}", evaluated)?,
                Err(e) => writeln!(writer, "{}", e)?,
            }
        }
    }
    Ok(())
}
