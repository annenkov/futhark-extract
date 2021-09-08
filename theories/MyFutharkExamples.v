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
From Coq Require Import Logic.Eqdep_dec.

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

  Definition max (x y : Z) : Z :=
    if x >? y then x else y.

  Lemma max_equiv:
    forall x y : Z, max x y = Z.max x y.
  Proof.
    intros x y; unfold max; unfold Z.max; unfold Z.gtb;
      destruct (x ?= y) eqn:H; try apply Z.compare_eq_iff in H;
      subst; reflexivity.
    Qed.

  Ltac destruct_ands H :=
    let C1 := fresh "C" in
    let C2 := fresh "C" in
    match type of H with
    | _ /\ _ => destruct H as [C1 C2]; destruct_ands C1; destruct_ands C2
    | _ => idtac
    end.

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
           | Eq : (_, _) = (_, _) |- _ => inversion Eq; clear Eq
           end.

  Ltac split_tuple_eq_goal :=
    repeat match goal with
           | |- (_, _) = (_, _) => f_equal
           end.

  Definition X__cond (x : Z * Z * Z * Z) : bool :=
    let '(x1, x2, x3, x4) := x in
    (x2 <=? x1) && (x3 <=? x1) && (0 <=? x2) && (0 <=? x3) && (x4 <=? x2) && (x4 <=? x3).

  Definition P__X (x : Z * Z * Z * Z) : Prop := X__cond x = true.

  Ltac destruct_bool B :=
    match type of B with
    | true = _    => apply eq_sym in B; destruct_bool B
    | false = _   => apply eq_sym in B; destruct_bool B
    | ?B0 = true  => let B1 := fresh "B" in
                    let B2 := fresh "B" in
                    match B0 with
                    | _ && _ => apply andb_true_iff in B; destruct B as [B1 B2]
                    | _ || _  => apply orb_true_iff  in B; destruct B as [B1 | B2]
                    | negb _ => apply negb_true_iff in B
                    | _ => fail
                    end;
                    try destruct_bool B1;
                    try destruct_bool B2
    | ?B0 = false => let B1 := fresh "B" in
                    let B2 := fresh "B" in
                    match B0 with
                    | _ && _ => apply andb_false_iff in B; destruct B as [B1 | B2]
                    | _ || _  => apply orb_false_iff  in B; destruct B as [B1 B2]
                    | negb _ => apply negb_false_iff in B
                    | _ => fail
                    end;
                    try destruct_bool B1;
                    try destruct_bool B2
    end.

  Ltac bool_const_right :=
    repeat match goal with
           | B : true  = _  |- _ => apply eq_sym in B
           | |-   true  = _      => apply eq_sym
           | B : false = _ |- _  => apply eq_sym in B
           | |-   false = _      => apply eq_sym
           end.

  Ltac convert_ineqb_to_ineq :=
    bool_const_right;
    repeat match goal with
           | B : (_ =?  _) = true |- _ => apply Z.eqb_eq  in B
           | B : (_ <?  _) = true |- _ => apply Z.ltb_lt  in B
           | B : (_ <=? _) = true |- _ => apply Z.leb_le  in B
           | B : (_ >?  _) = true |- _ => apply Z.gtb_ltb in B
           | B : (_ >=? _) = true |- _ => apply Z.geb_leb in B
           end.

  Ltac split_X_cond_goal :=
    repeat (apply andb_true_iff; split); apply Z.leb_le.

  Lemma X_cond_equiv:
    forall x : Z * Z * Z * Z, P__X x <-> let '(x1, x2, x3, x4) := x in
                    x2 <= x1 /\ x3 <= x1 /\ 0 <= x2 /\ 0 <= x3 /\ x4 <= x2 /\ x4 <= x3.
  Proof.
    intros; split; destruct_tuples; unfold P__X; unfold X__cond.
    * intros H; destruct_bool H; convert_ineqb_to_ineq; lia.
    * intros; split_X_cond_goal; lia.
  Qed.

  Definition X : Type := {x : Z * Z * Z * Z | P__X x }.

  Lemma X_proof_irrellevance:
    forall x y : X, proj1_sig x = proj1_sig y <-> x = y.
  Proof.
    split; intros;
      match goal with
      | x : X, y: X |- _ => destruct x; destruct y
      end;
      simpl in *;
      match goal with
      | |- exist _ _ _ = exist _ _ _ => subst; f_equal; apply (UIP_dec bool_dec)
      | H : exist _ _ _ = exist _ _ _ |- _ => inversion H; reflexivity
      end.
  Qed.

  Ltac destruct_X x :=
    let v := fresh "v" in
    let pf := fresh "pf" in
    destruct x as [v pf];
    unfold P__X in pf;
    (* unfold X__cond in pf; *)
    try match goal with
        | var := proj1_sig (exist _ v _) |- _ => simpl in var; subst var
        end;
    destruct_tuple v;
    simpl in *;
    try destruct_bool pf.

  Ltac destruct_Xs :=
    fold X in *;
    unfold P__X in *;
    unfold X__cond in *;
    repeat let x := fresh in
           match goal with
           | [ x : X |- _ ] => destruct_X x
           end;
    convert_ineqb_to_ineq.

  Program Definition redOp (x y : X) : X :=
    let '(mssx, misx, mcsx, tsx) := proj1_sig x in
    let '(mssy, misy, mcsy, tsy) := proj1_sig y in
    ( max mssx (max mssy (mcsx + misy))
    , max misx (tsx + misy)
    , max mcsy (mcsx + tsy)
    , tsx + tsy
    ).
  Next Obligation.
    intros;
      repeat rewrite max_equiv;
      destruct_Xs;
      destruct_tuple_eqs;
      subst;
      split_X_cond_goal; lia.
  Defined.
  Check redOp.

  Program Definition X__unit : X := (Z0, Z0, Z0, Z0).
  Next Obligation.
    simpl; unfold P__X; unfold X__cond; split_X_cond_goal; reflexivity.
  Defined.
  Check X__unit.

  #[refine]
  Instance X__monoid : @Utils.IsMonoid X redOp X__unit :=
    {| Utils.munit_left  := _;
       Utils.munit_right := _;
       Utils.massoc      := _
    |}.
  all: intros; apply X_proof_irrellevance; destruct_Xs; repeat rewrite max_equiv.
  * split_tuple_eq_goal; lia.
  * split_tuple_eq_goal; lia.
  * destruct_Xs. split_tuple_eq_goal; lia.
  (* all: intros; destruct_tuples; destruct_Xs; unfold redOp; simpl; split_tuple_eq_goal; lia. *)
  Defined.
  Check X__monoid.

  Program Definition mapOp (x : Z) : X :=
    ( max x 0
    , max x 0
    , max x 0
    , x).
  Next Obligation.
    unfold P__X; unfold X__cond;
      intros; split_X_cond_goal;
        repeat rewrite max_equiv;
        convert_ineqb_to_ineq; lia.
  Defined.
  Check mapOp.

  Definition mss (xs : list Z) : Z :=
    match proj1_sig (Utils.reduce redOp X__unit (map mapOp xs)) with
    | (x, _, _, _) => x
    end.

  Definition mss_prelude :=
    <$
      sig_defs;
      i64_ops
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
