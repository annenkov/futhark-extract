(* From Coq Require Import Lia. *)
From Coq Require Import List.

(* Import ListNotations. *)

Require Import Program.

Require Import FutharkUtils.
Require Import FutharkArrays.
Require Import FutharkMod.

Module FutharkSpecImpl : FutharkSpec.

  Program Definition map {A B : Type} {n : nat} (f : A -> B) (xs : [|n|]A) : [|n|]B :=
    List.map f xs.
  Next Obligation.
    rewrite List.map_length; reflexivity.
  Defined.

  Program Definition reduce
          {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}
          {n : nat} (xs : [|n|]A) : A :=
    fold_right op ne xs.

  Program Fixpoint scan
          {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}
          {n : nat} (xs : [|n|]A) : [|n|]A :=
    match xs, n with
    | [], 0 => []
    | h :: t, S n' => h :: map (op h) (@scan _ _ op ne _ n' t)
    | _, _ => !
    end.
  Next Obligation.
    simpl; f_equal; rewrite List.map_length; assumption.
  Defined.
  Next Obligation.
    destruct xs; [apply H2 | apply (H1 a xs (#|xs|))]; split; reflexivity.
  Defined.
  Next Obligation.
    unfold not; split; intros * []; discriminate.
  Defined.
  Next Obligation.
    unfold not; split; intros * []; discriminate.
  Defined.

  Section map_obligations.

  Context {A B : Type} `{Dec A} `{Dec B}.

  Lemma map_cons {n : nat}:
    forall (f : A -> B) (x : A) (xs : [|n|]A), map f (x [::] xs) = f x [::] map f xs.
  Proof.
    intros; apply proof_irrelevance; reflexivity.
  Qed.

  End map_obligations.

  Section reduce_obligations.

    Context {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Theorem reduce_monoid_homo_unit:
      forall (xs : [|0|]A), reduce op ne xs  = ne.
    Proof.
      intros [l len]; destruct l; unfold reduce; simpl; reflexivity + discriminate.
    Qed.

    Theorem reduce_cons:
      forall (n : nat) (x : A) (xs : [|n|]A),
        reduce op ne (x [::] xs) = op x (reduce op ne xs).
    Proof. intros; reflexivity. Qed.

  End reduce_obligations.

  Section scan_obligations.

    Context {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Theorem scan_cons:
      forall (n : nat) (x : A) (xs : [|n|]A),
        scan op ne (x [::] xs) = x [::] map (op x) (scan op ne xs).
    Proof.
      intros;
        apply proof_irrelevance;
        simpl;
        repeat f_equal;
        apply proof_irrelevance;
        reflexivity.
    Qed.

    Theorem scan_nil:
      forall xs : [|0|]A, scan op ne xs = nil_arr.
    Proof.
      intros [[]]; apply proof_irrelevance; discriminate + reflexivity.
    Qed.

  End scan_obligations.

End FutharkSpecImpl.

Module FutharkImpl := FutharkMod (FutharkSpecImpl).
