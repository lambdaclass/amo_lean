// Parametric Rust harness for trzk-generated ArithExpr kernels.
// The generated file is imported via #[path] so no proc-macro wiring is needed.
// Arity is selected by `--cfg arity="N"` at compile time so the call signature
// matches the kernel exactly.

#[path = "./generated.rs"]
mod generated;

use generated::arith_spec;

#[cfg(arity = "1")]
fn call(xs: &[isize]) -> isize {
    match xs {
        [x0] => arith_spec(*x0),
        _ => {
            eprintln!("expected 1 isize arg, got {}", xs.len());
            std::process::exit(2);
        }
    }
}

#[cfg(arity = "2")]
fn call(xs: &[isize]) -> isize {
    match xs {
        [x0, x1] => arith_spec(*x0, *x1),
        _ => {
            eprintln!("expected 2 isize args, got {}", xs.len());
            std::process::exit(2);
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let xs: Vec<isize> = args
        .iter()
        .map(|s| s.parse::<isize>().expect("argv must be isize"))
        .collect();

    println!("{}", call(&xs));
}
