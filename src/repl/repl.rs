use crate::lexer;
use crate::token;
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
        loop {
            let tok = l.next_token();
            if tok == token::Token::EOF {
                break;
            }
            write!(writer, "{:?}\n", tok).unwrap();
        }
    }
}
