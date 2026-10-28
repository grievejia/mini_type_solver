//! Command output and error checks for every subcommand.
//!
//! Tests use the same fixture files and keep result data separate from diagnostics.

mod common {
    //! Shared CLI expectation harness for the `parse`, `validate`, and
    //! `solve` tests.
    //!
    //! Each fixture is `<name>.input` plus `<name>.stdout` and `<name>.stderr`.
    //! Each directory has an explicit expected exit status. Mismatches print
    //! a line diff. `BLESS=1` regenerates expectations.
    //!
    //! Helpers scrub ambient `RUST_LOG` from every spawn; only tests that set
    //! it explicitly keep it, so a developer shell cannot pollute stderr
    //! expectations or blessed fixtures.

    use std::env;
    use std::fs;
    use std::io;
    use std::io::Write;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};

    use similar::TextDiff;

    /// Check one fixture directory against its expected exit status.
    pub fn check_dir(subcommand: &str, dir: &str, expected_status: i32) -> io::Result<()> {
        let mut inputs: Vec<PathBuf> = fs::read_dir(dir)?
            .collect::<io::Result<Vec<_>>>()?
            .into_iter()
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "input"))
            .collect();
        inputs.sort();
        for input in &inputs {
            check_fixture(subcommand, input, expected_status)?;
        }
        Ok(())
    }

    /// Prove `-` reads the same program as a file run.
    ///
    /// Compares against a fresh file run instead of the blessed stdout: the
    /// matrix test rewrites that file under `BLESS=1`.
    pub fn dash_matches_file_run(subcommand: &str, input: &Path) -> io::Result<()> {
        let bin = env!("CARGO_BIN_EXE_mini_type_solver");
        let program = fs::read(input)?;
        let from_file = Command::new(bin)
            .arg(subcommand)
            .arg(input)
            .env_remove("RUST_LOG")
            .output()?;
        assert_eq!(from_file.status.code(), Some(0));
        assert!(from_file.stderr.is_empty());

        let mut child = Command::new(bin)
            .arg(subcommand)
            .arg("-")
            .env_remove("RUST_LOG")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let mut stdin = child
            .stdin
            .take()
            .ok_or_else(|| io::Error::other("stdin was not piped"))?;
        stdin.write_all(&program)?;
        drop(stdin);
        let from_stdin = child.wait_with_output()?;
        assert_eq!(from_stdin.status.code(), Some(0));
        assert_eq!(from_stdin.stdout, from_file.stdout);
        assert!(from_stdin.stderr.is_empty());
        Ok(())
    }

    /// A missing `FILE` argument is a usage error: exit 2, empty stdout.
    pub fn missing_argument_exits_2(subcommand: &str) -> io::Result<()> {
        let output = Command::new(env!("CARGO_BIN_EXE_mini_type_solver"))
            .arg(subcommand)
            .env_remove("RUST_LOG")
            .output()?;
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
        Ok(())
    }

    /// A missing input file fails with exit 1, empty stdout, and a stderr
    /// line naming the path.
    pub fn missing_input_file(subcommand: &str) -> io::Result<()> {
        let missing_text = format!("tests/data/{subcommand}/does_not_exist.input");
        let missing = Path::new(&missing_text);
        let output = Command::new(env!("CARGO_BIN_EXE_mini_type_solver"))
            .arg(subcommand)
            .arg(missing)
            .env_remove("RUST_LOG")
            .output()?;
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8_lossy(&output.stderr);
        let prefix = format!("{}: ", missing.display());
        assert!(
            stderr.starts_with(&prefix),
            "stderr was: {stderr:?}, want prefix: {prefix:?}"
        );
        Ok(())
    }

    fn check_fixture(subcommand: &str, input: &Path, expected_status: i32) -> io::Result<()> {
        let output = Command::new(env!("CARGO_BIN_EXE_mini_type_solver"))
            .arg(subcommand)
            .arg(input)
            .env_remove("RUST_LOG")
            .output()?;
        let actual_stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let actual_stderr = String::from_utf8_lossy(&output.stderr)
            .replace(input.to_string_lossy().as_ref(), "<input>");
        assert_eq!(
            output.status.code(),
            Some(expected_status),
            "exit status for {}",
            input.display()
        );
        if env::var("BLESS").is_ok_and(|value| value == "1") {
            fs::write(input.with_extension("stdout"), &actual_stdout)?;
            fs::write(input.with_extension("stderr"), &actual_stderr)?;
            return Ok(());
        }
        let expected_stdout = fs::read_to_string(input.with_extension("stdout"))?;
        assert!(
            actual_stdout == expected_stdout,
            "stdout mismatch for {}:\n{}",
            input.display(),
            unified_diff(&expected_stdout, &actual_stdout)
        );
        let expected_stderr = fs::read_to_string(input.with_extension("stderr"))?;
        assert!(
            actual_stderr == expected_stderr,
            "stderr mismatch for {}:\n{}",
            input.display(),
            unified_diff(&expected_stderr, &actual_stderr)
        );
        Ok(())
    }

    fn unified_diff(expected: &str, actual: &str) -> String {
        let text_diff = TextDiff::from_lines(expected, actual);
        let mut unified = text_diff.unified_diff();
        unified.header("expected", "actual");
        unified.to_string()
    }
}

mod parse {
    //! CLI expectation harness for the `parse` subcommand.

    use super::common;

    use std::io;
    use std::path::Path;

    #[test]
    fn parse_fixtures() -> io::Result<()> {
        common::check_dir("parse", "tests/data/parse/valid", 0)?;
        common::check_dir("parse", "tests/data/parse/invalid", 1)
    }

    #[test]
    fn dash_reads_program_from_stdin() -> io::Result<()> {
        common::dash_matches_file_run("parse", Path::new("tests/data/parse/valid/example.input"))
    }

    #[test]
    fn missing_file_argument_exits_2() -> io::Result<()> {
        common::missing_argument_exits_2("parse")
    }

    #[test]
    fn missing_input_file() -> io::Result<()> {
        common::missing_input_file("parse")
    }
}

mod validate {
    //! CLI expectation harness for the `validate` subcommand.

    use super::common;

    use std::env;
    use std::fs;
    use std::io;
    use std::path::Path;
    use std::process::Command;

    #[test]
    fn validate_fixtures() -> io::Result<()> {
        common::check_dir("validate", "tests/data/validate/valid", 0)?;
        common::check_dir("validate", "tests/data/validate/invalid", 1)
    }

    #[test]
    fn show_mro_matches_declaration_companions() -> io::Result<()> {
        for name in ["example", "generic_classes"] {
            let input = format!("tests/data/validate/valid/{name}.input");
            let companion = format!("tests/data/validate/valid/{name}.mro");
            let output = Command::new(env!("CARGO_BIN_EXE_mini_type_solver"))
                .arg("validate")
                .arg("--show-mro")
                .arg(input)
                .output()?;
            assert_eq!(output.status.code(), Some(0));
            assert!(output.stderr.is_empty());
            let actual = String::from_utf8_lossy(&output.stdout).into_owned();
            if env::var("BLESS").is_ok_and(|value| value == "1") {
                fs::write(companion, &actual)?;
                continue;
            }
            let expected = fs::read_to_string(companion)?;
            assert_eq!(actual, expected, "mro mismatch for {name}");
            assert!(
                !actual
                    .lines()
                    .any(|line| line.starts_with("MRO(object) =")
                        || line.starts_with("MRO(never) =")),
                "built-ins must have no mro lines"
            );
        }
        Ok(())
    }

    #[test]
    fn dash_reads_program_from_stdin() -> io::Result<()> {
        common::dash_matches_file_run(
            "validate",
            Path::new("tests/data/validate/valid/example.input"),
        )
    }

    #[test]
    fn missing_file_argument_exits_2() -> io::Result<()> {
        common::missing_argument_exits_2("validate")
    }

    #[test]
    fn missing_input_file() -> io::Result<()> {
        common::missing_input_file("validate")
    }
}

mod solve {
    //! CLI expectation harness for the `solve` subcommand.

    use super::common;

    use std::fs;
    use std::io;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output};

    #[test]
    fn solve_fixtures() -> io::Result<()> {
        common::check_dir("solve", "tests/data/solve/sat", 0)?;
        common::check_dir("solve", "tests/data/solve/error", 1)?;
        common::check_dir("solve", "tests/data/solve/unsat", 0)
    }

    #[test]
    fn dash_reads_program_from_stdin() -> io::Result<()> {
        common::dash_matches_file_run("solve", Path::new("tests/data/solve/sat/design.input"))
    }

    #[test]
    fn missing_file_argument_exits_2() -> io::Result<()> {
        common::missing_argument_exits_2("solve")
    }

    #[test]
    fn missing_input_file() -> io::Result<()> {
        common::missing_input_file("solve")
    }

    /// Run `solve` over one fixture with an engine, extra arguments, and
    /// a controlled `RUST_LOG`: `None` for the engine uses the default,
    /// and `None` for the log removes the variable so ambient
    /// environments cannot leak into expectations.
    fn run_solve(
        input: &Path,
        engine: Option<&str>,
        extra_args: &[&str],
        rust_log: Option<&str>,
    ) -> io::Result<Output> {
        let mut command = Command::new(env!("CARGO_BIN_EXE_mini_type_solver"));
        command.arg("solve");
        if let Some(engine) = engine {
            command.arg("--engine").arg(engine);
        }
        command.args(extra_args);
        command.arg(input);
        match rust_log {
            Some(value) => {
                command.env("RUST_LOG", value);
            }
            None => {
                command.env_remove("RUST_LOG");
            }
        }
        command.output()
    }

    fn design_input() -> &'static Path {
        Path::new("tests/data/solve/sat/design.input")
    }

    /// Engine verdicts must match on every fixture and nothing else:
    /// models must be valid and cores subset-minimal per engine, which
    /// the solver unit tests pin; the CLI compares exit status and the
    /// verdict line only.
    #[test]
    fn engines_match_verdicts() -> io::Result<()> {
        for dir in ["tests/data/solve/sat", "tests/data/solve/unsat"] {
            let mut inputs: Vec<PathBuf> = fs::read_dir(dir)?
                .collect::<io::Result<Vec<_>>>()?
                .into_iter()
                .map(|entry| entry.path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "input"))
                .collect();
            inputs.sort();
            for input in &inputs {
                let mut verdicts = Vec::new();
                for engine in ["dnf", "direct", "varisat"] {
                    let output = run_solve(input, Some(engine), &[], None)?;
                    assert!(
                        output.stderr.is_empty(),
                        "{engine} stderr for {}: {:?}",
                        input.display(),
                        String::from_utf8_lossy(&output.stderr)
                    );
                    verdicts.push((output.status.code(), verdict(&output)));
                }
                for (engine, verdict) in ["direct", "varisat"].iter().zip(verdicts.iter().skip(1)) {
                    assert_eq!(
                        verdict,
                        &verdicts[0],
                        "{engine} disagrees with dnf for {}",
                        input.display()
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn invalid_restrictions_fail_before_engine_work() -> io::Result<()> {
        for name in ["restricted_scope_model", "restricted_scope_upper"] {
            let input = PathBuf::from(format!("tests/data/validate/invalid/{name}.input"));
            let expected = fs::read_to_string(input.with_extension("stderr"))?;
            for engine in ["dnf", "direct", "varisat"] {
                let output = run_solve(&input, Some(engine), &["--stats"], None)?;
                assert_eq!(output.status.code(), Some(1), "{engine}: {name}");
                assert!(output.stdout.is_empty(), "{engine}: {name}");
                let stderr = String::from_utf8_lossy(&output.stderr)
                    .replace(input.to_string_lossy().as_ref(), "<input>");
                assert_eq!(stderr, expected, "{engine}: {name}");
            }
        }
        Ok(())
    }

    /// First stdout line: the verdict the engines must share.
    fn verdict(output: &Output) -> String {
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .next()
            .unwrap_or("")
            .to_owned()
    }

    #[test]
    fn varisat_repeated_runs_are_byte_identical() -> io::Result<()> {
        let first = run_solve(design_input(), Some("varisat"), &[], None)?;
        let second = run_solve(design_input(), Some("varisat"), &[], None)?;
        assert_eq!(first.status.code(), Some(0));
        assert_eq!(second.status.code(), Some(0));
        assert_eq!(second.stdout, first.stdout, "varisat stdout differs");
        assert!(second.stderr.is_empty());
        Ok(())
    }

    #[test]
    fn tuple_model_repeated_runs_are_byte_identical() -> io::Result<()> {
        assert_repeated_model(Path::new("tests/data/solve/sat/tuple_model.input"), "tuple")
    }

    #[test]
    fn callable_model_repeated_runs_are_byte_identical() -> io::Result<()> {
        assert_repeated_model(
            Path::new("tests/data/solve/sat/callable_model.input"),
            "callable",
        )
    }

    #[test]
    fn generic_model_repeated_runs_are_byte_identical() -> io::Result<()> {
        assert_repeated_model(
            Path::new("tests/data/solve/sat/generic_model.input"),
            "generic",
        )
    }

    #[test]
    fn generic_class_model_repeated_runs_are_byte_identical() -> io::Result<()> {
        assert_repeated_model(
            Path::new("tests/data/solve/sat/generic_class_model.input"),
            "generic class",
        )
    }

    #[test]
    fn restricted_generic_model_repeated_runs_are_byte_identical() -> io::Result<()> {
        assert_repeated_model(
            Path::new("tests/data/solve/sat/restricted_generic_model.input"),
            "restricted generic",
        )
    }

    fn assert_repeated_model(input: &Path, kind: &str) -> io::Result<()> {
        for engine in ["dnf", "direct", "varisat"] {
            let first = run_solve(input, Some(engine), &[], None)?;
            let second = run_solve(input, Some(engine), &[], None)?;
            assert_eq!(first.status.code(), Some(0));
            assert_eq!(second.status.code(), Some(0));
            assert_eq!(second.stdout, first.stdout, "{engine} {kind} model differs");
            assert!(first.stderr.is_empty());
            assert!(second.stderr.is_empty());
        }
        Ok(())
    }

    #[test]
    fn info_level_keeps_stdout_byte_identical_with_progress_on_stderr() -> io::Result<()> {
        let plain = run_solve(design_input(), Some("dnf"), &[], None)?;
        let info = run_solve(design_input(), Some("dnf"), &["--log-level", "info"], None)?;
        assert_eq!(plain.status.code(), Some(0));
        assert_eq!(info.status.code(), Some(0));
        assert!(plain.stderr.is_empty());
        assert_eq!(info.stdout, plain.stdout);
        let stderr = String::from_utf8_lossy(&info.stderr);
        for needle in [
            "solving file",
            "assertions=7",
            "units=7",
            "metavars=3",
            "materialized DNF terms",
            "terms=2",
            "verdict=\"satisfiable\"",
        ] {
            assert!(
                stderr.contains(needle),
                "stderr lacks {needle:?}: {stderr:?}"
            );
        }
        // The default engine reports the same verdict on stdout with its
        // own summary on stderr.
        let direct = run_solve(design_input(), None, &["--log-level", "info"], None)?;
        assert_eq!(direct.status.code(), Some(0));
        assert_eq!(direct.stdout, plain.stdout);
        let direct_stderr = String::from_utf8_lossy(&direct.stderr);
        for needle in [
            "solving file",
            "assertions=7",
            "units=7",
            "metavars=3",
            "direct search complete",
            "branch_attempts=",
            "verdict=\"satisfiable\"",
        ] {
            assert!(
                direct_stderr.contains(needle),
                "direct stderr lacks {needle:?}: {direct_stderr:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn rust_log_debug_without_flag_enables_debug() -> io::Result<()> {
        let output = run_solve(design_input(), Some("dnf"), &[], Some("debug"))?;
        assert_eq!(output.status.code(), Some(0));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("term unsatisfiable"),
            "stderr lacks per-term lines: {stderr:?}"
        );
        assert!(
            stderr.contains("term satisfiable"),
            "stderr lacks per-term lines: {stderr:?}"
        );
        Ok(())
    }

    #[test]
    fn explicit_flag_beats_rust_log() -> io::Result<()> {
        let output = run_solve(
            design_input(),
            Some("dnf"),
            &["--log-level", "info"],
            Some("warn"),
        )?;
        assert_eq!(output.status.code(), Some(0));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("materialized DNF terms"),
            "stderr lacks info lines: {stderr:?}"
        );
        assert!(
            !stderr.contains("term satisfiable"),
            "debug lines leak past the flag: {stderr:?}"
        );
        Ok(())
    }

    #[test]
    fn invalid_rust_log_warns_and_falls_back() -> io::Result<()> {
        let plain = run_solve(design_input(), None, &[], None)?;
        let output = run_solve(design_input(), None, &[], Some("not-a-level=also-bad"))?;
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, plain.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("warning: ignoring invalid RUST_LOG"),
            "stderr lacks the fallback warning: {stderr:?}"
        );
        Ok(())
    }

    #[test]
    fn stats_leaves_stdout_identical_with_counters_on_stderr() -> io::Result<()> {
        for engine in [Some("dnf"), Some("direct"), Some("varisat"), None] {
            let plain = run_solve(design_input(), engine, &[], None)?;
            let stats = run_solve(design_input(), engine, &["--stats"], None)?;
            assert_eq!(stats.status.code(), Some(0));
            assert_eq!(stats.stdout, plain.stdout);
            assert!(
                !stats.stderr.is_empty(),
                "no counters on stderr for engine {engine:?}"
            );
        }
        Ok(())
    }

    /// Assert fixed line order, exact deterministic lines, and
    /// digits-only `elapsed_ms` (never an exact value).
    fn assert_exact_stats(stderr: &[u8], deterministic: &[&str]) {
        let text = String::from_utf8_lossy(stderr);
        let mut lines = text.lines();
        for expected in deterministic {
            match lines.next() {
                Some(line) => assert_eq!(line, *expected, "stats line"),
                None => panic!("stderr ends before {expected:?}: {text:?}"),
            }
        }
        match lines.next() {
            Some(line) => {
                let digits = line.strip_prefix("elapsed_ms=").unwrap_or("");
                assert!(
                    !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()),
                    "elapsed line has no digits-only value: {line:?}"
                );
            }
            None => panic!("stderr lacks elapsed_ms: {text:?}"),
        }
        assert!(lines.next().is_none(), "trailing stats lines: {text:?}");
    }

    #[test]
    fn stats_blocks_report_exact_counters() -> io::Result<()> {
        let empty = Path::new("tests/data/solve/sat/empty.input");
        let dnf = run_solve(empty, Some("dnf"), &["--stats"], None)?;
        assert_eq!(dnf.status.code(), Some(0));
        assert_exact_stats(
            &dnf.stderr,
            &[
                "engine=dnf",
                "materialized_terms=1",
                "theory_calls=1",
                "activated_atoms_sum=0",
                "peak_activated_atoms=0",
            ],
        );
        let direct = run_solve(empty, Some("direct"), &["--stats"], None)?;
        assert_eq!(direct.status.code(), Some(0));
        assert_exact_stats(
            &direct.stderr,
            &[
                "engine=direct",
                "branch_attempts=0",
                "backtracks=0",
                "theory_calls=1",
                "activated_atoms_sum=0",
                "peak_activated_atoms=0",
            ],
        );
        Ok(())
    }

    #[test]
    fn sat_stats_blocks_report_exact_counters() -> io::Result<()> {
        // The empty file holds no assertions: the degenerate path emits
        // no clauses, makes no solver calls, and checks the empty
        // activation once.
        let empty = Path::new("tests/data/solve/sat/empty.input");
        let sat = run_solve(empty, Some("varisat"), &["--stats"], None)?;
        assert_eq!(sat.status.code(), Some(0));
        let text = String::from_utf8_lossy(&sat.stderr);
        let mut lines = text.lines();
        assert_eq!(lines.next(), Some("engine=varisat"), "stats engine line");
        // The solver identity reports `<crate>-<version>` but the
        // test pins only its shape: asserting the exact version here
        // would just repeat the constant the binary already prints.
        let solver = lines.next().unwrap_or_else(|| {
            panic!("stderr lacks sat_solver: {text:?}");
        });
        assert!(
            solver
                .strip_prefix("sat_solver=varisat-")
                .is_some_and(|version| !version.is_empty()),
            "solver line shape: {solver:?}"
        );
        let rest = lines.collect::<Vec<_>>().join("\n") + "\n";
        assert_exact_stats(
            rest.as_bytes(),
            &[
                "sat_config=default",
                "sat_seed=none",
                "generated_clauses=0",
                "sat_calls=0",
                "theory_lemmas=0",
                "theory_calls=1",
                "activated_atoms_sum=0",
                "peak_activated_atoms=0",
            ],
        );
        Ok(())
    }

    #[test]
    fn invalid_engine_with_stats_exits_2() -> io::Result<()> {
        let output = run_solve(design_input(), Some("bogus"), &["--stats"], None)?;
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        Ok(())
    }

    #[test]
    fn explicit_flag_silences_invalid_rust_log() -> io::Result<()> {
        let output = run_solve(
            design_input(),
            Some("dnf"),
            &["--log-level", "info"],
            Some("not-a-level=also-bad"),
        )?;
        assert_eq!(output.status.code(), Some(0));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !stderr.contains("warning: ignoring"),
            "warning leaks past the flag: {stderr:?}"
        );
        assert!(
            stderr.contains("materialized DNF terms"),
            "stderr lacks info lines: {stderr:?}"
        );
        Ok(())
    }
}
