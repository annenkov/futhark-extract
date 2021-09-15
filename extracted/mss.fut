-- Maximum segment sum test
-- ==
-- input { [1i64,-2i64,3i64,4i64,-1i64,5i64,-6i64,1i64] }
-- output { 11i64 }

type sig_ 'a = a
let Exist = id
let addI64 (i : i64) (j : i64) = i + j
let subI64 (i : i64) (j : i64) = i - j
let multI64 (i : i64) (j : i64) = i * j
let divI64 (i : i64) (j : i64) = i / j
let leI64 (i : i64) (j : i64) = i <= j
let ltI64 (i : i64) (j : i64) = i < j
let geI64 (i : i64) (j : i64) = i >= j
let gtI64 (i : i64) (j : i64) = i > j
let eqI64 (i : i64) (j : i64) = i == j

type x = sig_ (((i64,i64),i64),i64)

let max (x : i64) (y : i64) = if gtbI64 x y then x else y

let redOp_aux (x : (((i64,i64),i64),i64)) (y : (((i64,i64),i64),i64)) = match x
case (p, tsx) -> (match p
case (p0, mcsx) -> (match p0
case (mssx, misx) -> (match y
case (p1, tsy) -> (match p1
case (p00, mcsy) -> (match p00
case (mssy, misy) ->  ( ( ((max mssx (max mssy (addI64 mcsx misy))), (max misx (addI64 tsx misy))), (max mcsy (addI64 mcsx tsy))), (addI64 tsx tsy)))))))

let redOp (x : x) (y : x) = (redOp_aux (id x) (id y))

let X__unit  =  ( ( (0i64, 0i64), 0i64), 0i64)

let mapOp (x : i64) =  ( ( ((max x 0i64), (max x 0i64)), (max x 0i64)), x)

let mss_core (xs : [] i64) = reduce redOp X__unit (map mapOp xs)

let mss (xs : [] i64) = match id (mss_core xs)
case (p, z) -> (match p
case (p0, z0) -> (match p0
case (x, z1) -> x))

let main = mss
