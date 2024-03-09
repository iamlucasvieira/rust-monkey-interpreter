use rust_monkey_interpreter::repl;

const ASCII_ART: &str = r#" 
   __  ___          __           
  /  |/  /__  ___  / /_____ __ __
 / /|_/ / _ \/ _ \/  '_/ -_) // /
/_/  /_/\___/_//_/_/\_\\__/\_, / 
                          /___/  
"#;
fn main() {
    println!("{}", ASCII_ART);
    let _ = repl::start(&mut std::io::stdin(), &mut std::io::stdout());
}
