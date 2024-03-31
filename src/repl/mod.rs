use crate::evaluator;
use crate::lexer;
use crate::parser;
use std::io::{self, BufRead, BufReader, Read, Write};

const PROMPT: &str = ">> ";

pub fn start<R: Read, W: Write>(reader: R, writer: &mut W) -> io::Result<()> {
    let mut reader = BufReader::new(reader);
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

        let mut lexer = lexer::Lexer::new(&line);
        let mut parser = parser::Parser::new(&mut lexer);

        match parser.parse_program() {
            Ok(program) => match evaluator::eval(&program) {
                Ok(evaluated) => {
                    writeln!(writer, "{}", evaluated)?;
                }
                Err(_) => {}
            },
            Err(_) => {}
        }
    }
    Ok(())
}
