type sig_ 'a = a
let Exist = id

let zip_concat_swap (n : i64) (m : i64) (xs : sig_ ([] i64)) (ys : sig_ ([] i64)) =
let k = n + m in -- added by hand (along with coercions below)
Exist ((id (zip (concat xs ys  :> [k]i64 ) (Exist ((id (concat ys xs  :> [k]i64)))))))

-- #[unsafe] is added by hand, but it's easy to just generate it, since it does not require any explicit type coercions
let main = #[unsafe] zip_concat_swap 2 2 [1,2] [3,4]
