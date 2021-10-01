From Coq Require Import ZArith.
From Coq Require Import List.

Require Import MssUtils.
Require Import FutharkUnsized.

Definition mss_core (xs : list Z) : X :=
  reduce redOp X__unit (map mapOp xs).

Definition mss (xs : list Z) : Z :=
  let '(x, _, _, _) := proj1_sig (mss_core xs) in
  x.
