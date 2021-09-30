From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import List.

Require Import FutharkUtils.
Require Import FutharkUnsized.
Require Import MssUnsizedDefinition.

Import ListNotations.

Open Scope Z.

(** From this point we prove functional correctness of the [mss] function*)
Inductive Segment {A : Type} : list A -> list A -> Type :=
| HeadSegment  : forall seg tail, Segment seg (seg ++ tail)
| InnerSegment : forall prefix seg lst, Segment seg lst -> Segment seg (prefix ++ lst).

#[refine]
Instance sum__monoid : IsMonoid Z (fun x y => x + y) 0 :=
  {| munit_left  := _;
     munit_right := _;
     massoc      := _
  |}.
all: lia.
Qed.

Definition sum (l : list Z) : Z :=
  reduce (fun x y => x + y) 0 l.

Lemma mss_core_cons:
  forall (h : Z) (t : list Z),
    mss_core (h :: t) = redOp (mapOp h) (mss_core t).
Proof.
  intros; unfold mss_core; reflexivity.
Qed.

Lemma mss_core_append:
  forall l1 l2 : list Z,
    mss_core (l1 ++ l2) = redOp (mss_core l1) (mss_core l2).
Proof.
  intros; unfold mss_core;
    rewrite map_app; rewrite reduce_monoid_homo_mult;
      reflexivity.
Qed.

Ltac destruct_mss_core l :=
  let x := fresh "x" in
  let eq := fresh "Eqx" in
  remember (mss_core l) as x eqn:eq;
  apply (f_equal proj1_sig) in eq;
  simpl in eq;
  destruct_X x.

Ltac destruct_mss_cores :=
  repeat (let l := fresh "l" in
          match goal with
          | |- context[mss_core ?l]
            => let x := fresh "x" in
              let eq := fresh "Eqx" in
              remember (mss_core l) as x eqn:eq;
              apply (f_equal proj1_sig) in eq
          end);
  destruct_Xs.

Lemma mss_pos:
  forall l : list Z, 0 <= mss l.
Proof.
  intros l; unfold mss; induction l.
  * simpl; reflexivity.
  * rewrite mss_core_cons; destruct_mss_cores; max_equiv_tac; lia.
Qed.

(* tactic for proving various results about how [mss] behaves
with respect to the append operation, via induction *)
Ltac mss_append_induction :=
  intros l1 l2; induction l1; simpl;
  [ (* Solve base cases *)
    apply Z.le_refl + apply mss_pos
  | (* Solve general cases *)
    unfold mss;
    repeat rewrite mss_core_cons;
    rewrite mss_core_append;
    destruct_mss_cores;
    repeat rewrite max_equiv;
    lia
  ].

Lemma mss_app_right:
  forall l1 l2 : list Z,  mss l1 <= mss (l1 ++ l2).
Proof. mss_append_induction. Qed.

Lemma mss_app_left:
  forall l1 l2 : list Z,  mss l2 <= mss (l1 ++ l2).
Proof. mss_append_induction. Qed.

Lemma mss_core_sum:
  forall l : list Z,
    let '(_, _, _, s) := proj1_sig (mss_core l) in
    s = sum l.
Proof.
  intros l; induction l.
  * simpl; reflexivity.
  * rewrite mss_core_cons; destruct_mss_core l; lia.
Qed.

Lemma mss_core_left:
  forall l : list Z,
    let '(_, x2, _, _) := proj1_sig (mss_core l) in
    exists l1 l2 : list Z, l = l1 ++ l2 /\ sum l1 = x2.
Proof.
  intros l; induction l.
  * simpl; exists []; exists []; auto.
  * rewrite mss_core_cons;
    destruct_mss_core l;
    (* We split up into tree case and solve these separately *)
    match goal with
    | |- context[max (max ?head 0) (?head + ?x4)]
      => (* First we assert that we are in one of these cases *)
        remember (max (max head 0) (head + x4)) as M eqn:EqM;
        assert (M_CASES : M = 0 \/ M = head \/ M = head + x4) by (max_equiv_tac; lia);
        clear EqM;
        (* Them we split up into these cases *)
        destruct_ors M_CASES;
        subst
    end.
    + (* CASE M = 0 *)
        exists []; exists (a :: l); simpl; split; reflexivity.
    + (* CASE M = a *)
      exists [a]; exists l; simpl. rewrite Z.add_0_r; split; reflexivity.
    + (* CASE M = a + e3 *)
      specialize IHl as [l1 [l2 [Happend Hsum]]].
      exists (a :: l1); exists l2; simpl; rewrite Happend; rewrite Hsum; split; reflexivity.
Qed.

Lemma mss_core_inner:
  forall l : list Z,
    let '(x1, _, _, _) := proj1_sig (mss_core l) in
    exists l1 l2 l3 : list Z, l = l1 ++ l2 ++ l3 /\ sum l2 = x1.
Proof.
  intros l; induction l as [|? ? IHl].
  * exists []; exists []; exists []; auto.
  * specialize (mss_core_left l) as Hleft;
    rewrite mss_core_cons;
    destruct_mss_core l;
    specialize IHl as [l1 [l2 [l3 [? ?]]]];
    rewrite max_add_right;
    simpl;
    (* We split up into tree case and solve these separately *)
    match goal with
    | |- context[max (max ?head 0) (max ?x1 (max (?head + ?x4) ?x4))]
      => (* First we assert that we are in one of these cases *)
        remember (max (max head 0) (max x1 (max (head + x4) x4))) as M eqn:EqM;
        assert (M_CASES : M = e \/ M = a \/ M = a + e3) by (max_equiv_tac; lia);
        clear EqM;
        (* Them we split up into these cases *)
        destruct_ors M_CASES;
        subst
    end.
    + (* CASE M = e *)
      exists (a :: l1); exists l2; exists l3;
        simpl; split; reflexivity.
    + (* CASE M = a *)
      exists []; exists [a]; exists (l1 ++ l2 ++ l3);
        simpl; rewrite Z.add_0_r; split; reflexivity.
    + (* CASE M = a + e3 *)
      specialize Hleft as [l1' [l2' [Happend Hsum]]].
      exists []; exists (a :: l1'); exists l2';
        simpl; rewrite Happend; rewrite Hsum; split; reflexivity.
Qed.

Lemma sum_vs_mss:
  forall l, sum l <= mss l.
Proof.
  intros l;
  specialize (mss_core_sum l).
  unfold mss;
  destruct_mss_core l;
  lia.
Qed.

(* TODO Is this the right way of doing it? *)
Local Hint Resolve mss_pos : core.
Local Hint Resolve sum_vs_mss : core.

Theorem mss_bound:
  forall X Y : list Z, Segment X Y -> sum X <= mss Y.
Proof.
  induction 1; simpl.
  * rewrite <- mss_app_right. eauto.
  * rewrite <- mss_app_left; eauto.
Qed.

Theorem mss_attain:
  forall l : list Z, exists s : list Z, exists pf : Segment s l,  sum s = mss l.
Proof.
  intros l;
  pose proof (mss_core_inner l) as H;
  unfold mss;
  destruct_mss_core l.
  specialize H as [? [s [? [? ?]]]];
  subst;
  exists s;
  exists (InnerSegment _ _ _ (HeadSegment _ _));
  reflexivity.
Qed.
