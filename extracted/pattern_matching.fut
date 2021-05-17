let addI64 (i : i64) (j : i64) = i + j
let subI64 (i : i64) (j : i64) = i - j
let multI64 (i : i64) (j : i64) = i * j
let divI64 (i : i64) (j : i64) = i / j
let leI64 (i : i64) (j : i64) = i <= j
let ltI64 (i : i64) (j : i64) = i < j
let eqI64 (i : i64) (j : i64) = i == j

type dec =
  #Yes i64
| #No i64


let add_dec (d1 : dec) (d2 : dec) = match d1
case #Yes i1 -> (match d2
case #Yes i2 -> (addI64 i1 i2)
case #No i2 -> (addI64 i1 i2))
case #No i1 -> (match d2
case #Yes i2 -> (addI64 i1 i2)
case #No i2 -> (addI64 i1 i2))

let main = add_dec (#Yes 10) (#No 5)
