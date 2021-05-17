-- Sum test
-- ==
--input { [4i64,3i64,2i64,1i64] }
-- output { 10i64 }

let addI64 (i : i64) (j : i64) = i + j
let subI64 (i : i64) (j : i64) = i - j
let multI64 (i : i64) (j : i64) = i * j
let divI64 (i : i64) (j : i64) = i / j
let leI64 (i : i64) (j : i64) = i <= j
let ltI64 (i : i64) (j : i64) = i < j
let eqI64 (i : i64) (j : i64) = i == j

let sum (xs : [] i64) = reduce addI64 0i64 xs

let main = sum
