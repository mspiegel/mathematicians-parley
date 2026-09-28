use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

use parley::said::Said;
use parley::source::Disk;

const USAGE: &str = "usage: parley check
       parley build [name] [set.mm]
       parley gate

Run from the working tree: the directory holding corpus/ and the proofs.";

fn exit(status: i32) -> ExitCode {
    ExitCode::from(u8::try_from(status).unwrap_or(1))
}

fn say(outcome: Said) -> ExitCode {
    let _ = std::io::stdout().write_all(outcome.printed.as_bytes());
    let _ = std::io::stderr().write_all(outcome.complained.as_bytes());
    exit(outcome.status)
}

fn refuse(why: &str) -> ExitCode {
    eprintln!("{why}\n\n{USAGE}");
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some((sub, rest)) = args.split_first() else {
        return refuse("no command given");
    };
    // At most this many arguments, for each command.
    let most = match sub.as_str() {
        "check" | "gate" => 0,
        "build" => 2,
        other => return refuse(&format!("unknown command {other}")),
    };
    if let Some(option) = rest.iter().find(|a| a.starts_with("--")) {
        return refuse(&format!("unknown option {option}"));
    }
    if rest.len() > most {
        return refuse(&format!("too many arguments: {}", rest[most..].join(" ")));
    }
    // Everything is read from where the command is run.
    let root = Path::new(".");
    match sub.as_str() {
        "check" => say(parley::check::run(&Disk::new(root.to_path_buf()))),
        "build" => say(parley::tools::build::run(
            root,
            rest.first().map(String::as_str),
            rest.get(1).map(String::as_str),
        )),
        _ => say(parley::tools::gate::run(root)),
    }
}
