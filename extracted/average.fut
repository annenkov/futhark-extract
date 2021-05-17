-- Average test
-- ==
--input { [10.5f64,20.5f64] }
-- output { 15.5f64 }

let addF64 (i : f64) (j : f64) = i + j
let subF64 (i : f64) (j : f64) = i - j
let multF64 (i : f64) (j : f64) = i * j
let divF64 (i : f64) (j : f64) = i / j
let eqF64 (a : f64 ) (b : f64 ) = a == b
let lebF64 (a : f64 ) (b : f64 ) = a <= b
let ltbF64 (a : f64 ) (b : f64 ) = a < b

let average (xs : [] f64) = divF64 (reduce addF64 0.0 xs) (f64.i64 (length xs))

let main = average
