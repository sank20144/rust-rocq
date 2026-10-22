use std::path::PathBuf;

pub fn sysroot() -> Option<String> {
    if let Ok(path) = std::env::var("SYSROOT") {
        return Some(path);
    }
    Some(env!("RUST_ROCQ_SYSROOT").to_owned())
}

pub fn without_incremental(args: Vec<String>) -> Vec<String> {
    let mut filtered = Vec::with_capacity(args.len());
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        if arg == "-C" || arg == "--codegen" {
            let Some(value) = args.next() else {
                filtered.push(arg);
                break;
            };
            if !value.starts_with("incremental=") {
                filtered.push(arg);
                filtered.push(value);
            }
        } else if arg.starts_with("-Cincremental=") || arg.starts_with("--codegen=incremental=") {
            continue;
        } else {
            filtered.push(arg);
        }
    }
    filtered
}

fn option_value(args: &[String], name: &str) -> Option<String> {
    for (i, arg) in args.iter().enumerate() {
        if arg == name {
            return args.get(i + 1).cloned();
        }
        if let Some(value) = arg.strip_prefix(&format!("{name}=")) {
            return Some(value.to_owned());
        }
    }
    None
}

fn codegen_value(args: &[String], name: &str) -> Option<String> {
    let prefix = format!("{name}=");
    for (i, arg) in args.iter().enumerate() {
        if arg == "-C" || arg == "--codegen" {
            if let Some(value) = args.get(i + 1).and_then(|v| v.strip_prefix(&prefix)) {
                return Some(value.to_owned());
            }
        }
        if let Some(value) = arg.strip_prefix(&format!("-C{prefix}")) {
            return Some(value.to_owned());
        }
        if let Some(value) = arg.strip_prefix(&format!("--codegen={prefix}")) {
            return Some(value.to_owned());
        }
    }
    None
}

fn path_component(value: &str) -> String {
    let component: String = value
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if component.is_empty() {
        "unknown".to_owned()
    } else {
        component
    }
}

pub fn cargo_output_dir(base: PathBuf, args: &[String]) -> PathBuf {
    let crate_name = option_value(args, "--crate-name").unwrap_or_else(|| "crate".to_owned());
    let metadata = codegen_value(args, "metadata").unwrap_or_else(|| "default".to_owned());
    base.join(path_component(&crate_name))
        .join(path_component(&metadata))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn removes_split_and_joined_incremental_options() {
        assert_eq!(
            without_incremental(strings(&[
                "rustc",
                "-C",
                "incremental=target/incremental",
                "-Copt-level=2",
                "--codegen=incremental=other",
                "input.rs",
            ])),
            strings(&["rustc", "-Copt-level=2", "input.rs"])
        );
    }

    #[test]
    fn cargo_output_uses_crate_name_and_metadata() {
        let output = cargo_output_dir(
            PathBuf::from("out"),
            &strings(&["--crate-name", "my_crate", "-C", "metadata=abc123"]),
        );
        assert_eq!(output, PathBuf::from("out/my_crate/abc123"));
    }
}
