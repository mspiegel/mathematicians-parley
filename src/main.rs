use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str = "usage: parley check [root]
       parley build [name] [set.mm]
       parley gate";

/// The root of the working tree: the directory holding `Cargo.toml`'s
/// corpus, found by walking up from where the command is run.
fn working_tree() -> PathBuf {
    let here = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut at = here.as_path();
    loop {
        if at.join("db").is_dir() && at.join("stdlib").is_dir() {
            return at.to_path_buf();
        }
        match at.parent() {
            Some(up) => at = up,
            None => return here,
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let _root = working_tree();
    match args.first().map(String::as_str) {
        Some("check") | Some("build") | Some("gate") => {
            eprintln!("not yet written");
            ExitCode::from(2)
        }
        _ => {
            eprintln!("{USAGE}");
            ExitCode::from(2)
        }
    }
}
