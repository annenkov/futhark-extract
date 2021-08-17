From Futhark Require Import FutharkExtract.
From Futhark Require Import FutharkPretty.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Utils.
From ConCert.Utils Require Import StringExtra.

From Coq Require Import Datatypes.
From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Arith.
From Coq Require Import Floats.
From Coq Require Import Lia.

From MetaCoq.Template Require Import MCString.
From MetaCoq.Template Require Import MCList.

From stdpp Require Import base.

Import ListNotations.

Open Scope string.
Open Scope pair_scope.

Definition float_zero := S754_zero false.

Definition nat_to_float : nat -> spec_float :=
    fun n => match n with
          | O => float_zero
          | S _ => S754_finite false (Pos.of_nat n) 0
          end.

(** We remap Coq's types to the corresponding Futhark types. *)
(*  All required operations should be remapped as well. *)
Definition TT :=
  [
  (* natural numbers *)
    remap <%% nat %%> "i64"
  ; remap <%% plus %%> "addI64"
  ; remap <%% mult %%> "multI64"

  (* integers *)
  ; remap <%% Z %%> "i64"
  ; remap <%% Z.add %%> "addI64"
  ; remap <%% Z.mul %%> "multI64"

  (* floats *)
  ; remap <%% spec_float %%> "f64"
  ; remap <%% float_zero %%> "0.0"
  ; remap <%% SF64add %%> "addF64"
  ; remap <%% SF64div %%> "divF64"
  ; remap <%% nat_to_float %%> "f64.i64"

  (* bools *)
  ; remap <%% bool %%> "bool"
  (* lists *)
  ; remap <%% list %%> "[]"
  ; remap <%% @List.length %%> "length"
  ; remap <%% List.fold_right %%> "reduce"

   (* subset types *)
  ; remap <%% sig %%> "sig_"
  ; remap <%% @proj1_sig %%> "id"
].

Definition TT_ctors :=
  [ ("O", "0i64")
  ; ("Z0", "0i64")
  ; ("true", "true")
  ; ("false", "false")].

Open Scope string.


Module Tuples.
  (** Example of how tuples of length greater than two are exported
      when deconstructed with match or let expressions.
   *)

  Definition tmatch (x : Z * Z * Z * Z) :=
    match x with
    | (y, _, _, _) => y
    end.

  Definition tlet (x : Z * Z * Z * Z) :=
    let '(y, _, _, _) := x in y.

  Definition twiceFirst (x : Z * Z * Z * Z) := (tmatch x, tlet x).

  MetaCoq Run (futhark_extraction "" "" TT []
                                  None
                                  twiceFirst).

End Tuples.


Module MaximumSegmentSum.

  (** Futhark implementation of maximum segment sum:

    -- Parallel maximum segment sum
    -- ==
    -- input { [1, -2, 3, 4, -1, 5, -6, 1] }
    -- output { 11 }

    let max(x: i32, y: i32): i32 =
      if x > y then x else y

    let redOp(x: (i32,i32,i32,i32))
            (y: (i32,i32,i32,i32)): (i32,i32,i32,i32) =
      let (mssx, misx, mcsx, tsx) = x in
      let (mssy, misy, mcsy, tsy) = y in
      ( max(mssx, max(mssy, mcsx + misy))
      , max(misx, tsx+misy)
      , max(mcsy, mcsx+tsy)
      , tsx + tsy)

    let mapOp (x: i32): (i32,i32,i32,i32) =
      ( max(x,0)
      , max(x,0)
      , max(x,0)
      , x)

    let main(xs: []i32): i32 =
      let (x, _, _, _) =
        reduce redOp (0,0,0,0) (map mapOp xs) in
      x
  *)


  Fixpoint map {T T' : Type} (f : T -> T') (arr : list T) : list T' :=
    match arr with
    | [] => []
    | x :: xs => f x :: map f xs
    end.

  Definition assoc_fun {T : Type} (eq_cond : T -> T -> Prop) (ne : T) (f : T -> T -> T) : Prop :=
    forall x y z : T,
      eq_cond (f x (f y z)) (f (f x y) z)
      /\ eq_cond (f x ne) x
      /\ eq_cond (f ne x) x.

  Fixpoint reduce
           {T : Type}
           {eq_cond : T -> T -> Prop}
           (ne : T)
           (f : T -> T -> T | assoc_fun eq_cond ne f)
           (ar : list T)
  : T :=
    match ar with
    | [] => ne
    | x :: xs => proj1_sig f x (reduce ne f xs)
    end.

  Open Scope Z.

  Definition Dom : Type :=
    {x : Z * Z * Z * Z |
      forall x1 x2 x3 x4 : Z,
        (x1, x2, x3, x4) = x -> (x1 >= x2 /\x1 >= x3 /\ x2 >= 0 /\ x3 >= 0 /\ x2 >= x4 /\ x3 >= x4)}.

  Ltac unfold_Dom :=
    repeat (match goal with
            | [ x : Dom |- _ ] => destruct x as [[[[? ?] ?] ?] ?]
            end).

  Program Definition DomUnit : Dom := (Z0, Z0, Z0, Z0).
  Next Obligation.
    intros x1 x2 x3 x4 H; inversion H; lia.
  Defined.
  Check DomUnit.

  Ltac compare_to_inequality :=
    repeat (match goal with
            | [ H : _ ?= _ = Eq |- _ ] => apply Z.compare_eq in H
            | [ H : ?a ?= ?b = Gt |- _ ] => fold (Z.gt a b) in H
            | [ H : ?a ?= ?b = Lt |- _ ] => fold (Z.lt a b) in H
            end).

  Definition eq_Dom (x : Dom) (y : Dom) : Prop :=
    proj1_sig x = proj1_sig y.

  Lemma proj1_sig_eq:
    forall x y : Dom, x = y -> proj1_sig x = proj1_sig y.
  Proof.
    intros; repeat (match goal with
                    | a : Dom |- _ => destruct a
                    end);
    simpl; match goal with
    | H : ?a = ?b |- _ => inversion H; trivial
    end.
  Qed.

  Lemma max_add_l:
    forall k n m : Z, k + Z.max n m = Z.max (k + n) (k + m).
  Proof.
    intros; unfold Z.max; rewrite Z.add_compare_mono_l;
        match goal with
        | |- context[?a ?= ?b] => destruct (a ?= b) eqn:?; trivial
        end.
  Qed.

  Lemma max_add_r:
    forall k n m : Z, Z.max n m + k = Z.max (n + k) (m + k).
  Proof.
    intros k n m; repeat rewrite (Z.add_comm _ k); apply max_add_l.
  Qed.

  Lemma max_elim:
    forall a b c : Z, b = c -> Z.max a b = Z.max a c.
  Proof.
    destruct 1; trivial.
  Qed.

  Ltac max_equality :=
    repeat rewrite <- Z.max_assoc;
    match goal with
    | |- ?a = ?a => trivial
    | |- Z.max ?a _ = Z.max ?a _ => apply max_elim; max_equality
    | |- Z.max ?a _ = Z.max ?b _ => rewrite (Z.max_comm a); max_equality
    end.

  Ltac add_max_equality :=
    repeat rewrite max_add_l;
    repeat rewrite max_add_r;
    repeat rewrite Z.add_assoc;
    max_equality.

  Program Definition redOp : { f : Dom -> Dom -> Dom | assoc_fun eq_Dom DomUnit f } :=
    fun (x y : Dom) =>
      let '(mssx, misx, mcsx, tsx) := proj1_sig x in
      let '(mssy, misy, mcsy, tsy) := proj1_sig y in
        ( Z.max mssx (Z.max mssy (mcsx + misy))
        , Z.max misx (tsx + misy)
        , Z.max mcsy (mcsx + tsy)
        , tsx + tsy).
  Next Obligation.
    intros; unfold_Dom;
      intros ? ? ? ? H; inversion H.
        repeat (match goal with
                | [H : (_, _, _, _) = ?a, I : forall _ _ _ _ : Z, (_, _, _, _) = ?a -> _ |- _]
                  (* Apply sub-type restrictions to tuples *)
                  => apply I in H
                end); lia.
  Defined.
  Next Obligation.
    simpl;
      match goal with
      | |- assoc_fun _ _ ?F => remember F as f
      end;
      unfold assoc_fun;
      intros;
      repeat split;
      repeat (match goal with
      | f : Dom -> Dom -> Dom |- eq_Dom (?f ?a (?f ?b ?c)) (?f (?f ?a ?b) ?c)
        => remember (f a b) as fab;
          remember (f fab c) as ffabc;
          remember (f b c) as fbc;
          remember (f a fbc) as fafbc
      | f : Dom -> Dom -> Dom |- eq_Dom (?f ?v ?w) _
        => remember (f v w) as fvw
      end);
      unfold_Dom;
      unfold eq_Dom;
      simpl in *;
      repeat f_equal;
      repeat (match goal with
              | [ f : Dom -> Dom -> Dom, f_def : ?f = _, Eq : _ = ?f _ _ |- _ ]
                => apply proj1_sig_eq in Eq; rewrite f_def in Eq; simpl in Eq; inversion Eq
              end);
      repeat (match goal with
              | H : forall _ _ _ _ : Z, (_, _, _, _) = (?a, ?b, ?c, ?d) -> _ |- _
                => specialize (H a b c d (@eq_refl _ _)) as [? [? [? [? [? ?]]]]]
              end);
      try add_max_equality;
    repeat rewrite (Z.add_comm _ 0); simpl;
    repeat match goal with
    | Ineq : ?a >= ?b |- context[Z.max ?a ?b] => rewrite (Zmax_left a b Ineq)
    | Ineq : ?a >= ?b |- context[Z.max ?b ?a] => rewrite (Z.max_comm b a); rewrite (Zmax_left a b Ineq)
    end; trivial. lia.
  Defined.
  Check redOp.

  Program Definition mapOp (x : Z) : Dom :=
    ( Z.max x 0
    , Z.max x 0
    , Z.max x 0
    , x).
  Next Obligation.
    intros; unfold Z.max; destruct (x ?= 0) as [] eqn:?; compare_to_inequality; intros;
      match goal with
      | H : (_, _, _, _) = (_, _, _, _) |- _ => inversion H
      end;
      lia.
  Defined.
  Check mapOp.

  Definition mss (xs : list Z) : Z :=
    match proj1_sig (reduce DomUnit redOp (map mapOp xs)) with
    | (x, _, _, _) => x
    end.

  Definition mss_prelude :=
    <$
      sig_defs;
      i64_ops;
      "let max(x: i32, y: i32): i32 = if x > y then x else y"
    $>.

  Definition TT_extra :=
    [ remap <%% @reduce %%> "reduce"
    ; remap <%% @map %%> "map"
    ; remap <%% @Z.max %%> "max"
    ].

  Definition test_input := [1; -2; 3; 4; -1; 5; -6; 1].
  Definition test_output := 11.

  Example mss_test : mss test_input = test_output. reflexivity. Qed.

  Definition futhark_mss_test :=
    {| FTname := "Maximum segment sum test"
     ; FTinput := string_of_list (fun n => string_of_Z n ++ "i64") test_input
     ; FToutput := string_of_Z test_output ++ "i64" |}.

  MetaCoq Run (futhark_extraction "" mss_prelude
                                  (TT ++ TT_extra) TT_ctors
                                  (Some futhark_mss_test)
                                  mss).

End MaximumSegmentSum.
