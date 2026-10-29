use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

use parley::said::Said;
use parley::source::Disk;

const USAGE: &str = "usage: parley check [name]
       parley build [name] [set.mm]
       parley gate
       parley renumber <theorem> <steps> <shift> [--dry-run]
         <steps> is 4.2..4.9, 4.2.. (to the end of its block) or 4.2;
         <shift> is +n or -n

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

/// `parley renumber <theorem> <steps> <shift> [--dry-run]`.
fn renumber(rest: &[String]) -> ExitCode {
    let dry = rest.iter().any(|a| a == "--dry-run");
    if let Some(option) = rest.iter().find(|a| a.starts_with("--") && *a != "--dry-run") {
        return refuse(&format!("unknown option {option}"));
    }
    let given: Vec<&String> = rest.iter().filter(|a| !a.starts_with("--")).collect();
    let [name, steps, by] = given.as_slice() else {
        return refuse("renumber takes a theorem, the steps to move and a shift");
    };
    let Some(run) = parley::tools::renumber::Run::parse(steps) else {
        return refuse(&format!("{steps} is not a run of steps: 4.2..4.9, 4.2.. or 4.2"));
    };
    let Some(by) = parley::tools::renumber::shift(by) else {
        return refuse(&format!("{by} is not a shift: +n or -n"));
    };
    say(parley::tools::renumber::run(Path::new("."), name, &run, by, dry))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some((sub, rest)) = args.split_first() else {
        return refuse("no command given");
    };
    if sub == "renumber" {
        return renumber(rest);
    }
    // At most this many arguments, for each command.
    let most = match sub.as_str() {
        "gate" => 0,
        "check" => 1,
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
        "check" => say(parley::checker::run_named(
            &Disk::new(root.to_path_buf()),
            rest.first().map(String::as_str),
        )),
        "build" => say(parley::tools::build::run(
            root,
            rest.first().map(String::as_str),
            rest.get(1).map(String::as_str),
        )),
        _ => say(parley::tools::gate::run(root)),
    }
}
