import "repl_iota"

let unsafe_index 'a (xs : []a) (i: i64) : a = #[unsafe] xs[i]
let map_wrapper 'a 'b (xs : []a) (f : a -> () -> b) : []b = map (\x -> f x ()) xs
type sig_ 'a = a
let Exist = id

let segm_replicate (n : i64) (reps : sig_ ([] i64)) (vs : sig_ ([] i64)) = let idxs = repl_iota reps in
map_wrapper (id idxs) (\i -> \Hin -> unsafe_index (id vs) (Exist (i)))

let main = segm_replicate
