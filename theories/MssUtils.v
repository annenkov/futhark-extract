From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Logic.Eqdep_dec.

From stdpp Require base.

Require Import Program.

Require Import FutharkUtils.

Open Scope bool_scope.
Open Scope Z.

Create HintDb mss.

Ltac mauto :=
  repeat (
      progress autounfold with futhark
      + (progress autounfold with mss)
      + (progress autorewrite with futhark)
      + (progress autorewrite with mss)
      + (progress auto with futhark)
      + (progress auto with mss)).

Definition max (x y : Z) : Z :=
  if x >? y then x else y.

Lemma max_equiv:
  forall x y : Z, max x y = Z.max x y.
Proof.
  intros x y; unfold max; unfold Z.max; unfold Z.gtb;
    destruct (x ?= y) eqn:H; try apply Z.compare_eq_iff in H;
    subst; reflexivity.
Qed.
Hint Rewrite max_equiv : futhark.

Ltac max_equiv_tac := repeat rewrite max_equiv in *.

Lemma max_add_right:
  forall a b c : Z, max a b + c = max (a + c) (b + c).
Proof. intros; max_equiv_tac; lia. Qed.
Hint Rewrite max_add_right : futhark.

Lemma max_add_left:
  forall a b c : Z, a + max b c = max (a + b) (a + c).
Proof. intros; max_equiv_tac; lia. Qed.
Hint Rewrite max_add_left : futhark.

Ltac destruct_ands H :=
  let C1 := fresh "C" in
  let C2 := fresh "C" in
  match type of H with
  | _ /\ _ => destruct H as [C1 C2]; destruct_ands C1; destruct_ands C2
  | _ => idtac
  end.

Ltac destruct_ors H :=
  let D1 := fresh "D" in
  let D2 := fresh "D" in
  match type of H with
  | _ \/ _ => destruct H as [D1 | D2]; try destruct_ors D1; try destruct_ors D2
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
  let '(mss, mis, mcs, ts) := x in
  (mis <=? mss) && (mcs <=? mss) && (0 <=? mis) && (0 <=? mcs) && (ts <=? mis) && (ts <=? mcs).

Definition P__X (x : Z * Z * Z * Z) : Prop := X__cond x = true.

Ltac destruct_bool B :=
  match type of B with
  | true = _    => apply eq_sym in B; destruct_bool B
  | false = _   => apply eq_sym in B; destruct_bool B
  | ?B0 = true  => let B1 := fresh "B" in
                  let B2 := fresh "B" in
                  match B0 with
                  | _ && _ => apply Bool.andb_true_iff in B; destruct B as [B1 B2]
                  | _ || _  => apply Bool.orb_true_iff  in B; destruct B as [B1 | B2]
                  | negb _ => apply Bool.negb_true_iff in B
                  | _ => fail
                  end;
                  try destruct_bool B1;
                  try destruct_bool B2
  | ?B0 = false => let B1 := fresh "B" in
                  let B2 := fresh "B" in
                  match B0 with
                  | _ && _ => apply Bool.andb_false_iff in B; destruct B as [B1 | B2]
                  | _ || _  => apply Bool.orb_false_iff  in B; destruct B as [B1 B2]
                  | negb _ => apply Bool.negb_false_iff in B
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
  repeat (apply Bool.andb_true_iff; split); apply Z.leb_le.

Lemma X_cond_equiv:
  forall x : Z * Z * Z * Z, P__X x <-> let '(mss, mis, mcs, ts) := x in
                  mis <= mss /\ mcs <= mss /\ 0 <= mis /\ 0 <= mcs /\ ts <= mis /\ ts <= mcs.
Proof.
  intros; split; destruct_tuples; unfold P__X; unfold X__cond.
  * intros H; destruct_bool H; convert_ineqb_to_ineq; lia.
  * intros; split_X_cond_goal; lia.
Qed.

Definition X : Type := {x : Z * Z * Z * Z | P__X x }.

Instance X_pi : SigEq P__X := SigEq_dec.

Ltac destruct_X_tuple x v pf :=
  destruct x as [v pf];
  (* in case we have bound the value in a let expression we get rid of the
  corresponding hypothesis *)
  try match goal with
      | var := proj1_sig (exist _ v _) |- _ => simpl in var; subst var
      end;
  destruct_tuple v.

(** tactic for destructing the tuple of an element in X and seperating out the
    inequalities in the condition. *)
Ltac destruct_X x :=
  let v := fresh "v" in
  let pf := fresh "pf" in
  destruct_X_tuple x v pf;
  simpl in *;
  apply X_cond_equiv in pf;
  destruct_ands pf.

(** tactic for destructing the tuple of an element in X and seperating out the
    inequalities in the condition. *)
Ltac destruct_Xs :=
  fold X in *;
  repeat (let x := fresh in
          match goal with
          | [ x : X |- _ ]
            => let v := fresh "v" in
              let pf := fresh "pf" in
              destruct_X_tuple x v pf
          end);
  simpl in *;
  repeat (let pf := fresh "pf" in
          match goal with
          | [pf : P__X _ |- _] => apply X_cond_equiv in pf; destruct_ands pf
          end).

(** operator for calculating the maximal segment sum with the reduce
    operation. The tuple values, (mss, mis, mcs, ts), should be understood as
    follows:
    - mss: Maximal Segment Sum
    - mis: Maximal Initial Sum (maximal sum of a left bounding segment)
    - mcs: Maximal Closing Sum (maximal sum of a right bounding segment)
    - ts:  Total Sum (of the elements of the array)
  *)
Definition redOp_aux (x y : Z * Z * Z * Z) : Z * Z * Z * Z :=
  let '(mssx, misx, mcsx, tsx) := x in
  let '(mssy, misy, mcsy, tsy) := y in
  ( max mssx (max mssy (mcsx + misy))
  , max misx (tsx + misy)
  , max mcsy (mcsx + tsy)
  , tsx + tsy
  ).

Program Definition redOp (x y : X) : X :=
  redOp_aux (proj1_sig x) (proj1_sig y).
Next Obligation.
  destruct_Xs;
    unfold P__X;
    unfold X__cond;
    repeat rewrite max_equiv;
    destruct_tuple_eqs;
    subst;
    split_X_cond_goal;
    lia.
Qed.

Definition X__unit : X := exist _ (Z0, Z0, Z0, Z0) eq_refl.

#[refine]
Instance X__monoid : IsMonoid X redOp X__unit :=
  {| munit_left  := _;
     munit_right := _;
     massoc      := _
  |}.
(* TODO This is really slow. Is it because I do not help [lia] enough? *)  (* goal 8 slow *)
all:
  intros;
  apply subset_eq;
  destruct_Xs;
  max_equiv_tac;
  split_tuple_eq_goal;
  lia.
Qed.

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
Qed.
