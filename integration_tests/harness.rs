// Parametric Rust harness for trzk-generated ArithExpr kernels.
// The generated file is imported via #[path] so no proc-macro wiring is needed.

#[path = "./generated.rs"]
mod generated;

use generated::arith_spec;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let xs: Vec<isize> = args
        .iter()
        .map(|s| s.parse::<isize>().expect("argv must be isize"))
        .collect();

    // arith_spec_1 takes 1 input.
    let y = match xs.as_slice() {
        [x0] => arith_spec(*x0),
        _ => {
            eprintln!("expected 1 isize arg, got {}", xs.len());
            std::process::exit(2);
        }
    };
    println!("{}", y);
}
