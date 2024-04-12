use clap::Parser;
use rust_monkey_interpreter::repl;
use std::fs::File;
use std::io::{self};

const ASCII_ART: &str = r#" 
   __  ___          __           
  /  |/  /__  ___  / /_____ __ __
 / /|_/ / _ \/ _ \/  '_/ -_) // /
/_/  /_/\___/_//_/_/\_\\__/\_, / 
                          /___/  
"#;

#[derive(Parser, Debug)]
#[command(
    name = "Monkey Interpreter",
    version = "1.0",
    author = "Lucas Vieira dos Santos"
)]
struct Args {
    ///Optional file to execute.
    /// If not provided, the REPL will be started
    #[arg(required = false)]
    file: Option<String>,
}

fn main() {
    env_logger::init();
    println!("{}", ASCII_ART);

    let args = Args::parse();

    match args.file {
        Some(file) => {
            let file = File::open(file).expect("File not found");
            let reader = io::BufReader::new(file);
            let _ = repl::start(reader, &mut std::io::stdout());
        }
        None => {
            let _ = repl::start(&mut std::io::stdin(), &mut std::io::stdout());
        }
    }
}
