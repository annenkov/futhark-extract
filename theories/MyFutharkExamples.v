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

Module Utils.

  Open Scope list_scope.

  (* Notation "x =s y" := (proj1_sig x = proj1_sig y) (at level 70, no associativity). *)

  Class IsMonoid__sig {A : Type} {P : A -> Prop} (op : sig P -> sig P -> sig P) (e : sig P) : Prop :=
    { munit_left__sig  : forall m, proj1_sig (op e m) = proj1_sig m;
      munit_right__sig : forall m, proj1_sig (op m e) = proj1_sig m;
      massoc__sig      : forall m1 m2 m3, proj1_sig (op m1 (op m2 m3)) = proj1_sig (op (op m1 m2) m3);
      mirlv_left__sig  : forall (m : sig P) (a : A) (p1 p2 : P a), proj1_sig (op (exist P a p1) m) = proj1_sig (op (exist P a p2) m);
      mirlv_right__sig : forall (m : sig P) (a : A) (p1 p2 : P a), proj1_sig (op m (exist P a p1)) = proj1_sig (op m (exist P a p2))
    }.

  Definition reduce__sig {A : Type} {P : A -> Prop} (op : sig P -> sig P -> sig P) (e : sig P) `{IsMonoid__sig A P op e} (xs : list (sig P)) :=
    fold_right op e xs.

  Theorem reduce_prop__sig:
    forall (A : Type) (P : A -> Prop) (op : sig P -> sig P -> sig P) (ne : sig P) (isM : IsMonoid__sig op ne) (l1 l2 : list (sig P)),
      proj1_sig (reduce__sig op ne (l1 ++ l2)) = proj1_sig (op (reduce__sig op ne l1) (reduce__sig op ne l2))
      /\ proj1_sig (reduce__sig op ne []) = proj1_sig ne.
  Proof.
    intros; split; auto;
      match goal with
      | |- context[?list1 ++ ?list2] => induction list1 as [|? ? IH]
      end;
      simpl.
    * rewrite munit_left__sig; trivial.
    * rewrite <- massoc__sig
      ; repeat match goal with
               | |- context[reduce__sig ?op ?ne ?list]
                 => let res := fresh "red" in
                   remember (reduce__sig op ne list) as res
               end
      ; match goal with
        | IH : proj1_sig ?r1 = proj1_sig ?r2 |- context[op _ ?r2]
          => let el1 := fresh "el" in
            let pf1 := fresh "pf" in
            let el2 := fresh "el" in
            let pf2 := fresh "pf" in
            destruct r1 as [el1 pf1]
            ; destruct r2 as [el2 pf2]
            ; simpl in IH; subst el1
            ; rewrite (mirlv_right__sig _ _ pf1 pf2)
        end
      ; reflexivity.
  Qed.

  Class IsMonoid (M : Type) (op : M -> M -> M) (e : M) : Prop :=
    { munit_left : forall m, (op e m) = m;
      munit_right : forall m, (op m e) = m;
      massoc : forall m1 m2 m3, op m1 (op m2 m3) = op (op m1 m2) m3
    }.

  Definition reduce {A : Type} (op : A -> A -> A) (e : A) `{IsMonoid A op e} (xs : list A) :=
    fold_right op e xs.

  Theorem reduce_prop:
    forall (A : Type) (op : A -> A -> A) (ne : A) (isM : IsMonoid A op ne) (l1 l2 : list A),
      reduce op ne (l1 ++ l2) = op (reduce op ne l1) (reduce op ne l2) /\ reduce op ne [] = ne.
  Proof.
    intros; split; auto;
      match goal with
      | |- context[?list1 ++ ?list2] => induction list1 as [|? ? IH]
      end;
      simpl.
    * rewrite munit_left; trivial.
    * rewrite IH; rewrite massoc; trivial.
  Qed.

End Utils.

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

  Open Scope Z.

  Ltac destruct_ands H :=
    let C1 := fresh "C" in
    let C2 := fresh "C" in
    match type of H with
    | _ /\ _ => destruct H as [C1 C2]; destruct_ands C1; destruct_ands C2
    | _ => idtac
    end.
    (* match goal with *)
    (* | H : _ /\ _ |- _ => destruct H *)
    (* end. *)

  Ltac destruct_tuple x :=
    let x1 := fresh "e" in
    let x2 := fresh "e" in
    match type of x with
    | (_ * _)%type  => destruct x as [x1 x2]; destruct_tuple x1; destruct_tuple x2
    | _ => idtac
    end.

  Ltac destruct_tuples :=
    repeat match goal with
    | t : (_ * _)%type |- _ => destruct_tuple t
    end.

  Ltac destruct_tuple_eqs :=
    repeat match goal with
           | Eq : (_, _) = (_, _) |- _ => inversion_clear Eq
           end.

  Ltac split_tuple_eq_goal :=
    repeat match goal with
           | |- (_, _) = (_, _) => f_equal
           end.

  Definition X : Type :=
    {x : Z * Z * Z * Z |
      forall x1 x2 x3 x4 : Z,
        (x1, x2, x3, x4) = x -> (x1 >= x2 /\x1 >= x3 /\ x2 >= 0 /\ x3 >= 0 /\ x2 >= x4 /\ x3 >= x4)}.

  Ltac destruct_X x :=
    let elm := fresh in
    let cond := fresh in
    destruct x as [elm cond];
    try match goal with
        | var := proj1_sig (exist _ elm _) |- _ => simpl in var; subst var
        end;
    destruct_tuple elm;
    match type of cond with
    | (forall _ _ _ _ : Z, (_, _, _, _) = (?z0, ?z1, ?z2, ?z3) -> _)
      => let cond' := fresh in
        specialize (cond z0 z1 z2 z3 (@eq_refl _ _)) as cond'; destruct_ands cond'
    end.

  Ltac destruct_Xs :=
    fold X in *;
    repeat
    let x := fresh in
    match goal with
    | [ x : X |- _ ] => destruct_X x
    end.

  Program Definition redOp (x y : X) : X :=
    let '(mssx, misx, mcsx, tsx) := proj1_sig x in
    let '(mssy, misy, mcsy, tsy) := proj1_sig y in
    ( Z.max mssx (Z.max mssy (mcsx + misy))
    , Z.max misx (tsx + misy)
    , Z.max mcsy (mcsx + tsy)
    , tsx + tsy
    ).
  Next Obligation.
    intros; destruct_Xs; intros; destruct_tuple_eqs; lia.
  Defined.
  Check redOp.

  Program Definition X__unit : X := (Z0, Z0, Z0, Z0).

  Next Obligation.
    simpl; inversion 1; lia.
  Defined.
  Check X__unit.

  #[refine]
  Instance X__monoid : @Utils.IsMonoid__sig (Z * Z * Z * Z) _ redOp X__unit :=
    {| Utils.munit_left__sig  := _;
       Utils.munit_right__sig := _;
       Utils.massoc__sig      := _;
       Utils.mirlv_left__sig  := _;
       Utils.mirlv_right__sig := _
    |}.
  all: intros; destruct_tuples; destruct_Xs; unfold redOp; simpl; split_tuple_eq_goal; lia.
  Defined.
  Check X__monoid.

  Program Definition mapOp (x : Z) : X :=
    ( Z.max x 0
    , Z.max x 0
    , Z.max x 0
    , x).
  Next Obligation.
    simpl; intros; destruct_tuple_eqs; lia.
  Defined.
  Check mapOp.

  Definition mss (xs : list Z) : Z :=
    match proj1_sig (Utils.reduce__sig redOp X__unit (map mapOp xs)) with
    | (x, _, _, _) => x
    end.

  Lemma max_justification:
    forall x y : Z, x > y -> Z.max x y = x.
  Proof. intros; lia. Qed.

  Definition mss_prelude :=
    <$
      sig_defs;
      i64_ops;
      "let max(x: i32, y: i32): i32 = if x > y then x else y"
    $>.

  Definition TT_extra :=
    [ remap <%% @Utils.reduce %%> "reduce"
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
