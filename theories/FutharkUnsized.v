From Coq Require Import List.

Import ListNotations.

Require Import FutharkUtils.

Definition reduce {A : Type} (op : A -> A -> A) (e : A) `{IsMonoid A op e} (xs : list A) : A :=
  fold_right op e xs.

(** The reduce function is multiplicative as a monoid homomorphism. *)
Theorem reduce_monoid_homo_mult (A : Type) (op : A -> A -> A) (ne : A) `{IsMonoid A op ne} :
  forall l1 l2 : list A, reduce op ne (l1 ++ l2) = op (reduce op ne l1) (reduce op ne l2).
Proof.
  intros l1 l2; induction l1 as [ |? ? IH]; simpl.
  * rewrite munit_left; trivial.
  * rewrite IH; rewrite massoc; trivial.
Qed.

(** From the multiplicative property of reduce, it behaves as follows with the
    cons operation. *)
Corollary reduce_monoid_homo_cons (A : Type) (op : A -> A -> A) (ne : A) `{IsMonoid A op ne} :
  forall (a : A) (l : list A), reduce op ne (a :: l) = op a (reduce op ne l).
Proof. intros; reflexivity. Qed.

(** The reduce function preserves the neutral element as a monoid homomorphism *)
Theorem reduce_monoid_homo_unit (A : Type) (op : A -> A -> A) (ne : A) `{IsMonoid A op ne} :
  reduce op ne [] = ne.
Proof. reflexivity. Qed.

(** For the filter function the [List.filter] function with the Lemmas
    [filter_In] and [filter_app] can probably do. *)
