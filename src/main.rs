use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;

use parley::said::Said;
use parley::source::Disk;

const USAGE: &str = "usage: parley check --root <dir>
       parley build --root <dir> [name] [set.mm]
       parley gate --root <dir>

<dir> is the working tree: the directory holding db/, stdlib/ and the proofs.";

/// A command line read: the root it names, and the arguments left over, in
/// order; or why it cannot be read.
struct Command {
    root: PathBuf,
    rest: Vec<String>,
}

/// Take `--root <dir>` (or `--root=<dir>`) out of the arguments after the
/// subcommand. It must be given exactly once and name a directory; anything
/// else that looks like an option is refused rather than taken for a name.
fn read(args: &[String]) -> Result<Command, String> {
    let mut root: Option<PathBuf> = None;
    let mut rest = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        let given = if arg == "--root" {
            i += 1;
            match args.get(i) {
                Some(dir) => Some(dir.clone()),
                None => return Err("--root needs a directory".into()),
            }
        } else {
            arg.strip_prefix("--root=").map(String::from)
        };
        match given {
            Some(dir) => {
                if root.is_some() {
                    return Err("--root is given more than once".into());
                }
                root = Some(PathBuf::from(dir));
            }
            None if arg.starts_with("--") => {
                return Err(format!("unknown option {arg}"))
            }
            None => rest.push(arg.clone()),
        }
        i += 1;
    }
    let root = root.ok_or("--root is required")?;
    if !root.is_dir() {
        return Err(format!("--root {} is not a directory", root.display()));
    }
    Ok(Command { root, rest })
}

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
    let Some((sub, after)) = args.split_first() else {
        return refuse("no command given");
    };
    // At most this many arguments besides the root, for each command.
    let most = match sub.as_str() {
        "check" | "gate" => 0,
        "build" => 2,
        other => return refuse(&format!("unknown command {other}")),
    };
    let command = match read(after) {
        Ok(command) => command,
        Err(why) => return refuse(&why),
    };
    if command.rest.len() > most {
        return refuse(&format!(
            "too many arguments: {}",
            command.rest[most..].join(" ")
        ));
    }
    let root = &command.root;
    match sub.as_str() {
        "check" => say(parley::check::run(&Disk::new(root.clone()))),
        "build" => say(parley::tools::build::run(
            root,
            command.rest.first().map(String::as_str),
            command.rest.get(1).map(String::as_str),
        )),
        _ => say(parley::tools::gate::run(root)),
    }
}
