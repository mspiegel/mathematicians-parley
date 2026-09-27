use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;

use parley::source::Disk;

const USAGE: &str = "usage: parley check [root]
       parley build [name] [set.mm]
       parley gate";

/// The root of the working tree: the nearest directory, from where the
/// command is run upwards, that holds the database and the library.
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

fn exit(status: i32) -> ExitCode {
    ExitCode::from(u8::try_from(status).unwrap_or(1))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("check") => {
            let root = args.get(1).map(PathBuf::from).unwrap_or_else(working_tree);
            let outcome = parley::check::run(&Disk::new(root));
            let _ = std::io::stdout().write_all(outcome.printed.as_bytes());
            let _ = std::io::stderr().write_all(outcome.complained.as_bytes());
            exit(outcome.status)
        }
        Some("build") | Some("gate") => {
            eprintln!("not yet written");
            ExitCode::from(2)
        }
        _ => {
            eprintln!("{USAGE}");
            ExitCode::from(2)
        }
    }
}
