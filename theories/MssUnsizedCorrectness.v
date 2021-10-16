From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import List.

Require Import FutharkUtils.
Require Import FutharkUnsized.
Require Import MssUtils.
Require Import MssUnsizedDefinition.

Import FutharkImpl.

Import ListNotations.

Open Scope Z.

(** From this point we prove functional correctness of the [mss] function*)
Inductive Segment {A : Type} : list A -> list A -> Type :=
| HeadSegment  : forall seg tail, Segment seg (seg ++ tail)
| InnerSegment : forall prefix seg lst, Segment seg lst -> Segment seg (prefix ++ lst).

Definition sum (l : list Z) : Z :=
  reduce (fun x y => x + y) 0 l.

Lemma sum_nil:
  sum [] = 0.
Proof.
  intros; unfold sum; mauto.
Qed.
Hint Rewrite sum_nil : mss.

Lemma sum_cons:
  forall (a : Z) (l : list Z), sum (a :: l) = a + sum l.
Proof.
  intros; unfold sum; mauto.
Qed.
Hint Rewrite sum_cons : mss.

Lemma sum_app:
  forall l1 l2 : list Z,
    sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  intros; unfold sum; mauto.
Qed.
Hint Rewrite sum_app : mss.

Lemma mss_core_nil:
  mss_core [] = X__unit.
Proof.
  intros; unfold mss_core; mauto.
Qed.
Hint Rewrite mss_core_nil : mss.

Lemma mss_core_cons:
  forall (h : Z) (t : list Z),
    mss_core (h :: t) = redOp (mapOp h) (mss_core t).
Proof.
  intros; unfold mss_core; mauto.
Qed.
Hint Rewrite mss_core_cons : mss.

Lemma mss_core_app:
  forall l1 l2 : list Z,
    mss_core (l1 ++ l2) = redOp (mss_core l1) (mss_core l2).
Proof.
  intros; unfold mss_core; mauto.
Qed.
Hint Rewrite mss_core_app : mss.

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

Ltac solve_for_mss_cores :=
  unfold mss in *;
  repeat (rewrite mss_core_nil + rewrite mss_core_cons + rewrite mss_core_app);
  destruct_mss_cores;
  max_equiv_tac;
  lia.

Lemma mss_pos:
  forall l : list Z, 0 <= mss l.
Proof.
  intros; solve_for_mss_cores.
Qed.

Lemma mss_app_right:
  forall (n : Z) (l1 l2 : list Z),  n <= mss l1 -> n <= mss (l1 ++ l2).
Proof.
  intros n [] l2; solve_for_mss_cores.
Qed.

Lemma mss_app_left:
  forall (n : Z) (l1 l2 : list Z),  n <= mss l2 -> n <= mss (l1 ++ l2).
Proof.
  intros n [] l2; solve_for_mss_cores.
Qed.

Lemma mss_core_sum:
  forall l : list Z,
    let '(_, _, _, s) := proj1_sig (mss_core l) in
    s = sum l.
Proof.
  intros l; induction l; mauto; solve_for_mss_cores.
Qed.

Hint Rewrite Z.add_0_r : mss.

Lemma mss_core_left:
  forall l : list Z,
    let '(_, x2, _, _) := proj1_sig (mss_core l) in
    exists l1 l2 : list Z, l = l1 ++ l2 /\ sum l1 = x2.
Proof.
  intros l; induction l; mauto.
  * simpl; exists []; exists []; mauto.
  * destruct_mss_core l;
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
        exists []; exists (a :: l); mauto.
    + (* CASE M = a *)
      exists [a]; exists l; simpl; mauto.
    + (* CASE M = a + e3 *)
      specialize IHl as [l1 [l2 [Happend Hsum]]].
      exists (a :: l1); exists l2; subst; mauto.
Qed.

Hint Rewrite Z.add_max_distr_r : mss.
Hint Rewrite Z.add_max_distr_l : mss.

Lemma mss_core_inner:
  forall l : list Z,
    let '(x1, _, _, _) := proj1_sig (mss_core l) in
    exists l1 l2 l3 : list Z, l = l1 ++ l2 ++ l3 /\ sum l2 = x1.
Proof.
  intros l; induction l as [|? ? IHl]; mauto.
  * exists []; exists []; exists []; mauto.
  * specialize (mss_core_left l) as Hleft;
    destruct_mss_core l;
    specialize IHl as [l1 [l2 [l3 [? ?]]]].
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
      exists (a :: l1); exists l2; exists l3; mauto.
    + (* CASE M = a *)
      exists []; exists [a]; exists (l1 ++ l2 ++ l3); mauto.
    + (* CASE M = a + e3 *)
      specialize Hleft as [l1' [l2' [Happend ?]]].
      exists []; exists (a :: l1'); exists l2'; subst; rewrite Happend; mauto.
Qed.

Lemma sum_vs_mss:
  forall l, sum l <= mss l.
Proof.
  intros l; specialize (mss_core_sum l); solve_for_mss_cores.
Qed.

Hint Resolve mss_pos : mss.
Hint Resolve sum_vs_mss : mss.
Hint Resolve mss_app_left : mss.
Hint Resolve mss_app_right : mss.

Theorem mss_bound:
  forall (s l : list Z), Segment s l -> sum s <= mss l.
Proof. induction 1; simpl; mauto. Qed.

Theorem mss_attain:
  forall l : list Z, exists (s : list Z) (pf : Segment s l),  sum s = mss l.
Proof.
  intros l;
  pose proof (mss_core_inner l) as H;
  unfold mss;
  destruct_mss_core l;
  specialize H as [? [s [? [? ?]]]];
  subst;
  exists s;
  exists (InnerSegment _ _ _ (HeadSegment _ _));
  reflexivity.
Qed.
