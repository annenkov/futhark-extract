let addI64 (i : i64) (j : i64) = i + j
let subI64 (i : i64) (j : i64) = i - j
let multI64 (i : i64) (j : i64) = i * j
let divI64 (i : i64) (j : i64) = i / j
let leI64 (i : i64) (j : i64) = i <= j
let ltI64 (i : i64) (j : i64) = i < j
let eqI64 (i : i64) (j : i64) = i == j

let dotprod (xs : [] i64) (ys : [] i64) = reduce addI64 0i64 (map2 multI64 xs ys)

let dotprod_list_of_pairs (xs : [] (i64,i64)) = let pair_of_lists = unzip xs in
dotprod pair_of_lists.0 pair_of_lists.1

let main = dotprod_list_of_pairs [ (1,4), (2,-5), (3,6) ]
