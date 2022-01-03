From Coq Require Import ZArith.

Require Import MssUtils.
Require Import FutharkArrays.
Require Import FutharkModImpl.

Import FutharkImpl.

Definition mss_core {n : nat} (xs : [|n|]Z) : X :=
  reduce redOp X__unit (map mapOp xs).

Definition mss {n : nat} (xs : [|n|]Z) : Z :=
  let '(x, _, _, _) := proj1_sig (mss_core xs) in
  x.

Definition mss_wrapper (xs : list Z) : Z :=
  mss (to_arr xs eq_refl).
