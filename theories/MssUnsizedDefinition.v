From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Logic.Eqdep_dec.

From stdpp Require base.

Require Import FutharkUtils.
Require Import FutharkUnsized.

Open Scope bool_scope.
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

Ltac max_equiv_tac := repeat rewrite max_equiv in *.

Lemma max_add_right:
  forall a b c : Z, max a b + c = max (a + c) (b + c).
Proof. intros; max_equiv_tac; lia. Qed.

Lemma max_add_left:
  forall a b c : Z, a + max b c = max (a + b) (a + c).
Proof. intros; max_equiv_tac; lia. Qed.

(* TODO I do not use this I think, so I should remove it. *)
Ltac max_add_normalize :=
  repeat rewrite max_add_right in *;
  repeat rewrite max_add_left in *;
  repeat rewrite Z.add_assoc in *.

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
  intros [] []; simpl; split; intros;
    match goal with
    | |- exist _ _ _ = exist _ _ _ => subst; f_equal; apply (UIP_dec Bool.bool_dec)
    | H : exist _ _ _ = exist _ _ _ |- _ => inversion H; reflexivity
    end.
Qed.

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
    operation. The tuple values, (x1, x2, x3, x4), should be understood as
    follows:
    - x1: maximal sum of a segment
    - x2: maximal sum of a left bounding segment
    - x3: maximal sum of a right bounding segment
    - x4: the total sum of the elements
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
  intros;
    destruct_Xs;
    unfold P__X;
    unfold X__cond;
    repeat rewrite max_equiv;
    destruct_tuple_eqs;
    subst;
    split_X_cond_goal;
    lia.
Qed.
Check redOp.

Program Definition X__unit : X := (Z0, Z0, Z0, Z0).
Next Obligation.
  simpl; unfold P__X; unfold X__cond; split_X_cond_goal; reflexivity.
Qed.
Check X__unit.

#[refine]
Instance X__monoid : IsMonoid X redOp X__unit :=
  {| munit_left  := _;
     munit_right := _;
     massoc      := _
  |}.
(* TODO This is really slow. Is it because I do not help [lia] enough? Goal 8
    is the slow one *)
all:
  intros;
  apply X_proof_irrellevance;
  destruct_Xs;
  max_equiv_tac;
  split_tuple_eq_goal;
  lia.
Qed.
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
Qed.
Check mapOp.

Definition mss_core (xs : list Z) : X :=
  reduce redOp X__unit (map mapOp xs).

Definition mss (xs : list Z) : Z :=
  let '(x, _, _, _) := proj1_sig (mss_core xs) in
  x.
