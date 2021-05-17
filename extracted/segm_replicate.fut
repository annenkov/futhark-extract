import "repl_iota"

-- hmm, it compiles without #[unsafe] as well ...
let unsafe_index 'a (xs : []a) (i: i64) : a = #[unsafe] xs[i]
let map_wrapper 'a 'b (xs : []a) (f : a -> () -> b) : []b = map (\x -> f x ()) xs
type sig_ 'a = a
let Exist = id

-- the first argument is dummy, it's just an artifact of erasure (we can optimise it away later)
let segm_replicate (n : i64) (reps : sig_ ([] i64)) (vs : sig_ ([] i64)) = let idxs = repl_iota reps in
map_wrapper (id idxs) (\i -> \Hin -> unsafe_index (id vs) (Exist (i)))

let main = segm_replicate 0 [1,2,3] [3,2,1]
