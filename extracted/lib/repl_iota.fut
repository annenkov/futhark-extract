-- taken from here: https://github.com/diku-dk/futhark-array19/blob/master/src/segm.fut

let segm_scan [n] 't (op: t -> t -> t) (ne: t)
              (flags: [n]bool)
              (as: [n]t) : [n]t =
  zip flags as
  |> scan (\(x_flag,x) (y_flag,y) ->
            (x_flag || y_flag,
             if y_flag then y else x `op` y))
     (false, ne)
  |> unzip |> (.1)

let repl_iota [n] (reps:[n]i64) : []i64 =
  let s1 = scan (+) 0 reps
  let s2 = map (\i -> if i==0 then 0
                     else #[unsafe] s1[i-1]) (iota n)
  let tmp = scatter (replicate (reduce (+) 0 reps) 0)
                    s2 (iota n)
  let flags = map (>0) tmp
  in segm_scan (+) 0 flags tmp