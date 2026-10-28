//! Criterion benchmarks for every solver input in `benchmarks/<set>/`.
//!
//! Set directories contain inputs directly. Benchmark names include the set.
//! Each engine must return the declared verdict before its timing starts.
//! Parsing and validation are not timed. Each timing includes one complete
//! solver call and the destruction of its report.

use std::ffi::OsStr;
use std::fs;
use std::hint::black_box;
use std::path::PathBuf;
use std::process::ExitCode;

use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion};
use mini_type_solver::frontend::{self, ValidatedFile};
use mini_type_solver::solver::{self, SolveOutcome, SolveReport};

const SAT_HEADER: &str = "# verdict: satisfiable";
const UNSAT_HEADER: &str = "# verdict: unsatisfiable";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Satisfiable,
    Unsatisfiable,
}

#[derive(Debug)]
struct Case {
    name: String,
    path: PathBuf,
    file: ValidatedFile,
    expected: Verdict,
}

fn load_cases() -> Result<Vec<Case>, String> {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benchmarks");
    let entries = fs::read_dir(&directory).map_err(|error| {
        format!(
            "failed to read benchmark directory {}: {error}",
            directory.display()
        )
    })?;

    let mut paths = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            format!(
                "failed to read an entry in benchmark directory {}: {error}",
                directory.display()
            )
        })?;
        let set = entry.path();
        let file_type = entry.file_type().map_err(|error| {
            format!(
                "failed to read benchmark entry type {}: {error}",
                set.display()
            )
        })?;
        if !file_type.is_dir() {
            continue;
        }
        let inputs = fs::read_dir(&set)
            .map_err(|error| format!("failed to read benchmark set {}: {error}", set.display()))?;
        let mut set_paths = Vec::new();
        for input in inputs {
            let path = input
                .map_err(|error| {
                    format!(
                        "failed to read an entry in benchmark set {}: {error}",
                        set.display()
                    )
                })?
                .path();
            if path.extension() == Some(OsStr::new("input")) {
                set_paths.push(path);
            }
        }
        if set_paths.is_empty() {
            return Err(format!(
                "benchmark set {} contains no .input files",
                set.display()
            ));
        }
        paths.extend(set_paths);
    }
    paths.sort();
    if paths.is_empty() {
        return Err(format!(
            "benchmark directory {} contains no benchmark sets",
            directory.display()
        ));
    }

    paths
        .into_iter()
        .map(|path| {
            let relative_path = path.strip_prefix(&directory).map_err(|error| {
                format!(
                    "benchmark path {} is outside {}: {error}",
                    path.display(),
                    directory.display()
                )
            })?;
            let name = relative_path
                .with_extension("")
                .to_str()
                .ok_or_else(|| format!("benchmark path is not valid UTF-8: {}", path.display()))?
                .to_owned();
            let source = fs::read_to_string(&path).map_err(|error| {
                format!("failed to read benchmark input {}: {error}", path.display())
            })?;
            let expected = match source.lines().next() {
                Some(SAT_HEADER) => Verdict::Satisfiable,
                Some(UNSAT_HEADER) => Verdict::Unsatisfiable,
                _ => {
                    return Err(format!(
                        "benchmark input {} must start with `{SAT_HEADER}` or `{UNSAT_HEADER}`",
                        path.display()
                    ));
                }
            };
            let display_path = path.display().to_string();
            let file = frontend::parse(&source)
                .and_then(frontend::validate)
                .map_err(|diagnostic| diagnostic.render(&display_path, &source))?;
            Ok(Case {
                name,
                path,
                file,
                expected,
            })
        })
        .collect()
}

fn bench_engine<S, F>(group: &mut BenchmarkGroup<'_, WallTime>, case: &Case, engine: &str, solve: F)
where
    F: Fn(&ValidatedFile) -> SolveReport<S>,
{
    let actual = match solve(&case.file).outcome() {
        SolveOutcome::Satisfiable(_) => Verdict::Satisfiable,
        SolveOutcome::Unsatisfiable(_) => Verdict::Unsatisfiable,
    };
    assert_eq!(
        actual,
        case.expected,
        "{engine} returned the wrong verdict for {}",
        case.path.display()
    );

    group.bench_function(engine, |bencher| {
        bencher.iter(|| solve(black_box(&case.file)));
    });
}

fn run() -> Result<(), String> {
    let mut criterion = Criterion::default().configure_from_args();
    for case in load_cases()? {
        let mut group = criterion.benchmark_group(case.name.as_str());
        bench_engine(&mut group, &case, "dnf", solver::solve_dnf);
        bench_engine(&mut group, &case, "direct", solver::solve_direct);
        bench_engine(&mut group, &case, "varisat", solver::solve_varisat);
        group.finish();
    }
    criterion.final_summary();
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
