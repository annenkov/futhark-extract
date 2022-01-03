

let tmatch (x : (((i64,i64),i64),i64)) = match x
case (p, z) -> (match p
case (p0, z0) -> (match p0
case (y, z1) -> y))

let tlet (x : (((i64,i64),i64),i64)) = match x
case (p, z) -> (match p
case (p0, z0) -> (match p0
case (y, z1) -> y))

let twiceFirst (x : (((i64,i64),i64),i64)) =  ((tmatch x), (tlet x))

let main = twiceFirst
