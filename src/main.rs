//! Thin command-line frontend for the solver core.

#![expect(
    clippy::multiple_crate_versions,
    reason = "varisat 0.2.2 pins syn 1/2 alongside the graph's syn 3"
)]

use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand, ValueEnum};
use mini_type_solver::frontend::{self, Diagnostic};
use mini_type_solver::solver;
use tracing_subscriber::{filter::EnvFilter, fmt};

#[derive(Debug, Parser)]
#[command(
    name = "mini_type_solver",
    version,
    about = "Prototype constraint solver"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Parse an input file and print the AST.
    Parse {
        /// Input file to parse, or `-` for standard input.
        file: PathBuf,
    },
    /// Validate an input file and print a summary.
    Validate {
        /// Input file to validate, or `-` for standard input.
        file: PathBuf,
        /// Print C3 linearizations after the summary.
        #[arg(long)]
        show_mro: bool,
    },
    /// Solve an input file and print the verdict.
    Solve {
        /// Input file to solve, or `-` for standard input.
        file: PathBuf,
        /// Progress-logging verbosity; beats `RUST_LOG` when present.
        #[arg(long)]
        log_level: Option<LogLevel>,
        /// Boolean engine: direct search (default), eager DNF, or
        /// lazy SAT over varisat.
        #[arg(long, value_enum, default_value = "direct")]
        engine: Engine,
        /// Print engine work counters as `key=value` lines on stderr.
        #[arg(long)]
        stats: bool,
    },
}

/// Boolean engine for the `solve` subcommand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Engine {
    Dnf,
    Direct,
    Varisat,
}

/// Progress-logging verbosity for the `solve` subcommand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum LogLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

impl LogLevel {
    /// Lowercase `EnvFilter` directive naming this level.
    fn directive(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warn => "warn",
            Self::Info => "info",
            Self::Debug => "debug",
            Self::Trace => "trace",
        }
    }
}

/// Choose the logging filter: an explicit flag wins, then a valid
/// nonempty `RUST_LOG`, then `warn`. Returns the invalid value when
/// `RUST_LOG` was present but unparsable, which the caller warns about
/// on stderr.
fn select_level(flag: Option<LogLevel>, rust_log: Option<&str>) -> (EnvFilter, Option<&str>) {
    if let Some(level) = flag {
        return (EnvFilter::new(level.directive()), None);
    }
    match rust_log {
        Some(value) if !value.is_empty() => match EnvFilter::try_new(value) {
            Ok(filter) => (filter, None),
            Err(_) => (EnvFilter::new("warn"), Some(value)),
        },
        _ => (EnvFilter::new("warn"), None),
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Commands::Parse { file } => parse_command(&file),
        Commands::Validate { file, show_mro } => validate_command(&file, show_mro),
        Commands::Solve {
            file,
            log_level,
            engine,
            stats,
        } => solve_command(&file, log_level, engine, stats),
    }
}

fn parse_command(file: &Path) -> ExitCode {
    let Some(source) = read_source(file) else {
        return ExitCode::from(1);
    };
    let path = file.display().to_string();
    match frontend::parse(&source) {
        Ok(parsed) => {
            println!("{parsed:#?}");
            ExitCode::SUCCESS
        }
        Err(diagnostic) => report(&path, &source, &diagnostic),
    }
}

fn validate_command(file: &Path, show_mro: bool) -> ExitCode {
    let Some(source) = read_source(file) else {
        return ExitCode::from(1);
    };
    let path = file.display().to_string();
    let parsed = match frontend::parse(&source) {
        Ok(parsed) => parsed,
        Err(diagnostic) => return report(&path, &source, &diagnostic),
    };
    match frontend::validate(parsed) {
        Ok(validated) => {
            println!("{}", validated.render_summary());
            if show_mro {
                print!("{}", validated.render_mro());
            }
            ExitCode::SUCCESS
        }
        Err(diagnostic) => report(&path, &source, &diagnostic),
    }
}

/// Read one input file (or standard input) into a string.
///
/// Prints the I/O or UTF-8 failure and returns `None` when reading fails.
fn read_source(file: &Path) -> Option<String> {
    let path = file.display().to_string();
    let bytes: io::Result<Vec<u8>> = if file == Path::new("-") {
        let mut buf = Vec::new();
        io::stdin().lock().read_to_end(&mut buf).map(|_| buf)
    } else {
        fs::read(file)
    };
    let bytes = match bytes {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("{path}: {error}");
            return None;
        }
    };
    match String::from_utf8(bytes) {
        Ok(source) => Some(source),
        Err(error) => {
            let offset = error.utf8_error().valid_up_to();
            eprintln!("{path}: invalid UTF-8 at byte {offset}");
            None
        }
    }
}

fn solve_command(
    file: &Path,
    log_level: Option<LogLevel>,
    engine: Engine,
    stats: bool,
) -> ExitCode {
    let rust_log = env::var("RUST_LOG").ok();
    let (filter, invalid) = select_level(log_level, rust_log.as_deref());
    if let Some(value) = invalid {
        eprintln!("warning: ignoring invalid RUST_LOG {value:?}; falling back to warn");
    }
    fmt()
        .with_env_filter(filter)
        .with_writer(io::stderr)
        // Plain output: logs stay deterministic when piped or matched.
        .with_ansi(false)
        .init();
    let Some(source) = read_source(file) else {
        return ExitCode::from(1);
    };
    let path = file.display().to_string();
    let parsed = match frontend::parse(&source) {
        Ok(parsed) => parsed,
        Err(diagnostic) => return report(&path, &source, &diagnostic),
    };
    match frontend::validate(parsed) {
        Ok(validated) => {
            match engine {
                Engine::Dnf => {
                    let report = solver::solve_dnf(&validated);
                    print!("{}", report.outcome().render(&source));
                    if stats {
                        print_dnf_stats(&report);
                    }
                }
                Engine::Direct => {
                    let report = solver::solve_direct(&validated);
                    print!("{}", report.outcome().render(&source));
                    if stats {
                        print_direct_stats(&report);
                    }
                }
                Engine::Varisat => {
                    let report = solver::solve_varisat(&validated);
                    print!("{}", report.outcome().render(&source));
                    if stats {
                        print_sat_stats(&report);
                    }
                }
            }
            ExitCode::SUCCESS
        }
        Err(diagnostic) => report(&path, &source, &diagnostic),
    }
}

/// Print DNF work counters as `key=value` lines in fixed order.
fn print_dnf_stats(report: &solver::SolveReport<solver::DnfStats>) {
    let engine = report.engine_stats();
    eprintln!("engine=dnf");
    eprintln!("materialized_terms={}", engine.materialized_terms());
    print_shared_stats(report.shared_stats());
}

/// Print direct-search work counters as `key=value` lines in fixed
/// order.
fn print_direct_stats(report: &solver::SolveReport<solver::DirectStats>) {
    let engine = report.engine_stats();
    eprintln!("engine=direct");
    eprintln!("branch_attempts={}", engine.branch_attempts());
    eprintln!("backtracks={}", engine.backtracks());
    print_shared_stats(report.shared_stats());
}

/// Print SAT work counters as `key=value` lines in fixed order:
/// engine identity and configuration, engine counters, then the
/// shared counters.
fn print_sat_stats(report: &solver::SolveReport<solver::SatStats>) {
    let stats = report.engine_stats();
    eprintln!("engine=varisat");
    eprintln!("sat_solver={}", solver::VARISAT_SOLVER);
    eprintln!("sat_config=default");
    eprintln!("sat_seed=none");
    eprintln!("generated_clauses={}", stats.generated_clauses());
    eprintln!("sat_calls={}", stats.sat_calls());
    eprintln!("theory_lemmas={}", stats.theory_lemmas());
    print_shared_stats(report.shared_stats());
}

/// Print engine-neutral work counters as `key=value` lines.
fn print_shared_stats(shared: &solver::SharedStats) {
    eprintln!("theory_calls={}", shared.theory_calls());
    eprintln!("activated_atoms_sum={}", shared.activated_atoms_sum());
    eprintln!("peak_activated_atoms={}", shared.peak_activated_atoms());
    eprintln!("elapsed_ms={}", shared.elapsed_ms());
}

/// Report one diagnostic on stderr. The caller returns exit 1.
fn report(path: &str, source: &str, diagnostic: &Diagnostic) -> ExitCode {
    eprintln!("{}", diagnostic.render(path, source));
    ExitCode::from(1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tracing_subscriber::filter::LevelFilter;

    fn solve_args(extra: &[&str]) -> Commands {
        let mut argv = vec!["mini_type_solver", "solve", "input.mts"];
        argv.extend_from_slice(extra);
        let Ok(cli) = Cli::try_parse_from(argv) else {
            panic!("expected solve arguments to parse");
        };
        cli.command
    }

    #[test]
    fn omitted_flag_parses_to_none() {
        let Commands::Solve {
            file, log_level, ..
        } = solve_args(&[])
        else {
            panic!("expected a solve command");
        };
        assert_eq!(file, PathBuf::from("input.mts"));
        assert_eq!(log_level, None);
    }

    #[test]
    fn every_level_parses_by_name() {
        for (name, level) in [
            ("error", LogLevel::Error),
            ("warn", LogLevel::Warn),
            ("info", LogLevel::Info),
            ("debug", LogLevel::Debug),
            ("trace", LogLevel::Trace),
        ] {
            let Commands::Solve { log_level, .. } = solve_args(&["--log-level", name]) else {
                panic!("expected a solve command");
            };
            assert_eq!(log_level, Some(level), "level {name} parses");
        }
    }

    #[test]
    fn engine_defaults_to_direct_and_parses_by_name() {
        let Commands::Solve { engine, .. } = solve_args(&[]) else {
            panic!("expected a solve command");
        };
        assert_eq!(engine, Engine::Direct);
        for (name, expected) in [
            ("dnf", Engine::Dnf),
            ("direct", Engine::Direct),
            ("varisat", Engine::Varisat),
        ] {
            let Commands::Solve { engine, .. } = solve_args(&["--engine", name]) else {
                panic!("expected a solve command");
            };
            assert_eq!(engine, expected, "engine {name} parses");
        }
    }

    /// One selection case: flag, `RUST_LOG`, expected level, reported value.
    type SelectionCase<'a> = (
        Option<LogLevel>,
        Option<&'a str>,
        LevelFilter,
        Option<&'a str>,
    );

    #[test]
    fn level_selection_prefers_flag_then_env_then_warn() {
        let cases: [SelectionCase<'_>; 11] = [
            (None, None, LevelFilter::WARN, None),
            (None, Some(""), LevelFilter::WARN, None),
            (None, Some("error"), LevelFilter::ERROR, None),
            (None, Some("warn"), LevelFilter::WARN, None),
            (None, Some("info"), LevelFilter::INFO, None),
            (None, Some("debug"), LevelFilter::DEBUG, None),
            (None, Some("trace"), LevelFilter::TRACE, None),
            (
                None,
                Some("mini_type_solver=debug"),
                LevelFilter::DEBUG,
                None,
            ),
            (
                None,
                Some("not-a-level=also-bad"),
                LevelFilter::WARN,
                Some("not-a-level=also-bad"),
            ),
            (Some(LogLevel::Info), Some("debug"), LevelFilter::INFO, None),
            (Some(LogLevel::Error), None, LevelFilter::ERROR, None),
        ];
        for (flag, rust_log, level, invalid) in cases {
            let (filter, invalid_value) = select_level(flag, rust_log);
            assert_eq!(
                filter.max_level_hint(),
                Some(level),
                "flag {flag:?} with RUST_LOG {rust_log:?} selects {level:?}"
            );
            assert_eq!(
                invalid_value, invalid,
                "flag {flag:?} with RUST_LOG {rust_log:?} reports {invalid:?}"
            );
        }
    }
}
