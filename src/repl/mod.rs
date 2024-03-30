use crate::ast::Node;
use crate::lexer;
use crate::parser;
use std::io::{BufRead, BufReader, Read, Result, Write};

const PROMPT: &str = ">> ";

pub fn start(reader: &mut dyn Read, writer: &mut dyn Write) -> Result<()> {
    let mut buff = BufReader::new(reader);
    loop {
        write!(writer, "{}", PROMPT)?;
        writer.flush()?;

        let mut line = String::new();
        match buff.read_line(&mut line) {
            Ok(0) => return Ok(()),
            Ok(_) => {}
            Err(e) => return Err(e),
        }

        let mut l = lexer::Lexer::new(&line);
        let mut p = parser::Parser::new(&mut l);

        if let Ok(p) = p.parse_program() {
            writeln!(writer, "{}", p.string())?;
        }
    }
}
