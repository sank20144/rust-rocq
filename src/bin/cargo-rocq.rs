use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

const USAGE: &str = "rust-rocq Cargo frontend

Usage:
    cargo rocq [--rocq-out <directory>] [--include-deps] -- [cargo check options]

Examples:
    cargo rocq
    cargo rocq --rocq-out out/my-project -- --workspace --all-features
    cargo rocq -- --manifest-path ../project/Cargo.toml

By default only Cargo's primary packages are translated. Dependencies are
compiled normally. --include-deps also translates dependency crates.";

#[derive(Debug, PartialEq, Eq)]
struct Options {
    out_dir: PathBuf,
    include_deps: bool,
    cargo_args: Vec<OsString>,
}

fn absolute(path: PathBuf) -> Result<PathBuf, String> {
    if path.is_absolute() {
        Ok(path)
    } else {
        env::current_dir()
            .map(|cwd| cwd.join(path))
            .map_err(|e| format!("could not determine the current directory: {e}"))
    }
}

fn parse_args(args: impl IntoIterator<Item = OsString>) -> Result<Option<Options>, String> {
    let mut args = args.into_iter().peekable();
    if args.peek().is_some_and(|a| a == "rocq") {
        args.next();
    }

    let mut out_dir = env::var_os("RUST_ROCQ_OUT").map(PathBuf::from);
    let mut include_deps = false;
    let mut cargo_args = Vec::new();
    let mut after_separator = false;

    while let Some(arg) = args.next() {
        if after_separator {
            cargo_args.push(arg);
            continue;
        }
        if arg == "--" {
            after_separator = true;
        } else if arg == "-h" || arg == "--help" {
            return Ok(None);
        } else if arg == "--include-deps" {
            include_deps = true;
        } else if arg == "--rocq-out" {
            let Some(path) = args.next() else {
                return Err("--rocq-out requires a directory".to_owned());
            };
            out_dir = Some(PathBuf::from(path));
        } else {
            cargo_args.push(arg);
        }
    }

    let out_dir = absolute(out_dir.unwrap_or_else(|| PathBuf::from("target/rocq")))?;
    Ok(Some(Options {
        out_dir,
        include_deps,
        cargo_args,
    }))
}

fn sibling_driver() -> Result<PathBuf, String> {
    let mut path = env::current_exe()
        .map_err(|e| format!("could not locate cargo-rocq: {e}"))?
        .with_file_name("rust-rocq");
    if cfg!(windows) {
        path.set_extension("exe");
    }
    if path.is_file() {
        Ok(path)
    } else {
        Err(format!(
            "rust-rocq driver not found next to cargo-rocq: {}",
            path.display()
        ))
    }
}

fn prepend_library_path(command: &mut Command, directory: &Path) -> Result<(), String> {
    let mut paths = vec![directory.to_path_buf()];
    if let Some(existing) = env::var_os("LD_LIBRARY_PATH") {
        paths.extend(env::split_paths(&existing));
    }
    let value = env::join_paths(paths).map_err(|e| format!("invalid library path: {e}"))?;
    command.env("LD_LIBRARY_PATH", value);
    Ok(())
}

fn run(options: Options) -> Result<ExitCode, String> {
    let driver = sibling_driver()?;
    let mut command = Command::new(env!("RUST_ROCQ_CARGO"));
    command.arg("check").args(&options.cargo_args);
    command.env("RUSTC", &driver);
    command.env("RUST_ROCQ_CARGO_MODE", "1");
    command.env("RUST_ROCQ_OUT", &options.out_dir);
    command.env("CARGO_INCREMENTAL", "0");
    if options.include_deps {
        command.env("RUST_ROCQ_INCLUDE_DEPS", "1");
    }
    prepend_library_path(
        &mut command,
        &Path::new(env!("RUST_ROCQ_SYSROOT")).join("lib"),
    )?;

    let status = command
        .status()
        .map_err(|e| format!("could not run {}: {e}", env!("RUST_ROCQ_CARGO")))?;
    Ok(ExitCode::from(status.code().unwrap_or(1) as u8))
}

fn main() -> ExitCode {
    match parse_args(env::args_os().skip(1)) {
        Ok(None) => {
            println!("{USAGE}");
            ExitCode::SUCCESS
        }
        Ok(Some(options)) => match run(options) {
            Ok(code) => code,
            Err(e) => {
                eprintln!("cargo-rocq: {e}");
                ExitCode::FAILURE
            }
        },
        Err(e) => {
            eprintln!("cargo-rocq: {e}\n\n{USAGE}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(xs: &[&str]) -> Vec<OsString> {
        xs.iter().map(OsString::from).collect()
    }

    #[test]
    fn cargo_subcommand_name_is_optional() {
        let with = parse_args(args(&["rocq", "--", "--workspace"]))
            .unwrap()
            .unwrap();
        let without = parse_args(args(&["--", "--workspace"])).unwrap().unwrap();
        assert_eq!(with.cargo_args, without.cargo_args);
    }

    #[test]
    fn separates_frontend_and_cargo_options() {
        let options = parse_args(args(&[
            "rocq",
            "--rocq-out",
            "generated",
            "--include-deps",
            "--",
            "--manifest-path",
            "fixture/Cargo.toml",
        ]))
        .unwrap()
        .unwrap();
        assert!(options.out_dir.ends_with("generated"));
        assert!(options.include_deps);
        assert_eq!(
            options.cargo_args,
            args(&["--manifest-path", "fixture/Cargo.toml"])
        );
    }

    #[test]
    fn accepts_cargo_options_without_separator() {
        let options = parse_args(args(&["rocq", "--manifest-path", "fixture/Cargo.toml"]))
            .unwrap()
            .unwrap();
        assert_eq!(
            options.cargo_args,
            args(&["--manifest-path", "fixture/Cargo.toml"])
        );
    }
}
