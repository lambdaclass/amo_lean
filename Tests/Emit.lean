import TRZK.Emit

open TRZK

#guard collectVars (.add (.var 1) (.var 0)) == #[0, 1]
#guard collectVars (.add (.var 2) (.add (.var 0) (.var 2))) == #[0, 2]
#guard collectVars (.const 5) == #[]
#guard collectVars (.mul (.var 1) (.var 0)) == #[0, 1]
#guard collectVars (.mul (.var 2) (.mul (.var 0) (.var 2))) == #[0, 2]

#guard emitFunction "arith_spec" (.const 0) == "pub fn arith_spec() -> isize { 0isize }"
#guard emitFunction "arith_spec" (.var 0) == "pub fn arith_spec(x0: isize) -> isize { x0 }"
#guard emitFunction "arith_spec" (.add (.var 0) (.var 1)) == "pub fn arith_spec(x0: isize, x1: isize) -> isize { (x0 + x1) }"
#guard emitFunction "arith_spec" (.add (.var 0) (.const 0)) == "pub fn arith_spec(x0: isize) -> isize { (x0 + 0isize) }"
#guard emitFunction "arith_spec" (.const (-5)) == "pub fn arith_spec() -> isize { (-5isize) }"
#guard emitFunction "arith_spec" (.add (.var 0) (.const (-1))) == "pub fn arith_spec(x0: isize) -> isize { (x0 + (-1isize)) }"
#guard emitFunction "arith_spec" (.mul (.var 0) (.var 1)) == "pub fn arith_spec(x0: isize, x1: isize) -> isize { (x0 * x1) }"
#guard emitFunction "arith_spec" (.mul (.var 0) (.const 1)) == "pub fn arith_spec(x0: isize) -> isize { (x0 * 1isize) }"
#guard emitFunction "arith_spec" (.mul (.var 0) (.const (-2))) == "pub fn arith_spec(x0: isize) -> isize { (x0 * (-2isize)) }"
