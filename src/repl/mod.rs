use crate::environment::Environment;
use crate::evaluator;
use crate::lexer;
use crate::parser;
use std::io::{self, BufRead, BufReader, Read, Write};

const PROMPT: &str = ">> ";

pub fn start<R: Read, W: Write>(reader: R, writer: &mut W) -> io::Result<()> {
    let mut reader = BufReader::new(reader);
    let mut env = Environment::new();
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
            match evaluator::eval(program.into(), &mut env) {
                Ok(evaluated) => writeln!(writer, "{}", evaluated)?,
                Err(e) => writeln!(writer, "{}", e)?,
            }
        }
    }
    Ok(())
}
