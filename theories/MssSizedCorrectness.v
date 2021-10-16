From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import ZArith.

Require Import FutharkArrays.
Require Import FutharkUtils.
Require Import FutharkModImpl.
Require Import MssUtils.
Require Import MssSizedDefinition.

Import FutharkImpl.

Open Scope Z.

(** TODO The types [Segment] and [Prefix] should maybe be moved to the Arrays
module. *)

(** From this point we prove functional correctness of the [mss] function*)
Inductive Segment {A : Type} : forall (n1 n2 : nat), ([|n1|]A) -> ([|n2|]A) -> Prop :=
| SegmentHead : forall (n1 n2 : nat) (l1 : [|n1|]A) (l2 : [|n2|]A),
    Prefix n1 n2 l1 l2 -> Segment n1 n2 l1 l2
| SegmentInner : forall (n1 n2 : nat) (h : A) (l1 : [|n1|]A) (l2 : [|n2|]A),
    Segment n1 n2 l1 l2 -> Segment n1 (S n2) l1 (h [::] l2).

Hint Constructors Segment : futhark.

Definition sum {n : nat} (l : [|n|]Z) : Z :=
  reduce (fun x y => x + y) 0 l.

Lemma sum_nil:
  forall (l : [|0%nat|]Z), sum l = 0.
Proof.
  intros; unfold sum; mauto.
  (* intros; nil_eq_tac; unfold sum; fauto. *)
Qed.
Hint Rewrite sum_nil : mss.

Lemma sum_cons:
  forall (n : nat) (a : Z) (l : [|n|]Z), sum (a [::] l) = a + sum l.
Proof.
  intros; unfold sum; mauto.
Qed.
Hint Rewrite sum_cons : mss.

Lemma mss_core_nil:
  forall (t : [|0%nat|]Z),
    mss_core t = exist P__X (0, 0, 0, 0) eq_refl.
Proof.
  intros; unfold mss_core; mauto.
Qed.
Hint Rewrite @mss_core_nil : mss.

Lemma mss_core_cons {n : nat}:
  forall (h : Z) (t : [|n|]Z),
    mss_core (h [::] t) = redOp (mapOp h) (mss_core t).
Proof.
  intros; unfold mss_core; mauto.
Qed.
Hint Rewrite @mss_core_cons : mss.

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

(** TODO make using [mss_core_cons] a part of this. *)
Ltac solve_for_mss_cores :=
    destruct_mss_cores;
    repeat rewrite max_equiv;
    lia.

(** TODO This is only used once, maybe inline it. *)
Lemma mss_cons_r {n : nat}:
  forall (h : Z) (l : [|n|]Z),
    mss l <= mss (h [::] l).
Proof.
  intros; unfold mss; mauto; solve_for_mss_cores.
Qed.
Hint Rewrite @mss_cons_r : mss.

Hint Resolve Z.add_0_r : mss.

Lemma mss_core_left {n : nat}:
  forall l : [|n|]Z,
    let '(_, x2, _, _) := proj1_sig (mss_core l) in
    exists (n' : nat) (l' : [|n'|]Z), Prefix n' n l' l /\ sum l' = x2.
Proof.
  intros l; induction n, l using arr_ind; mauto; simpl.
  * exists 0%nat. exists nil_arr; split; mauto.
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
      exists 0%nat; exists nil_arr; split; mauto.
    + (* CASE M = a *)
      exists 1%nat; exists (a [::] nil_arr); split; mauto; simpl; mauto.
    + (* CASE M = a + e3 *)
      specialize IHl as [n1 [l1 [Happend Hsum]]];
        subst; exists (S n1); exists (a [::] l1); split; mauto.
Qed.

Lemma mss_core_inner {n : nat}:
  forall l : [|n|]Z,
    let '(x1, _, _, _) := proj1_sig (mss_core l) in
    exists (n' : nat) (l' : [|n'|]Z), Segment n' n l' l /\ sum l' = x1.
Proof.
  intros l;
    induction n, l as [l|n h l IH] using arr_ind;
    mauto;
    destruct_mss_cores;
    simpl.
  * exists 0%nat; exists nil_arr; split; mauto.
  * specialize (mss_core_left l) as Hleft;
    destruct_mss_core l;
    specialize IH as [n' [l' [Hsegment Hsum]]];
    rewrite max_add_right;
    simpl;
    (* We split up into tree case and solve these separately *)
    match goal with
    | |- context[max (max ?head 0) (max ?x1 (max (?head + ?x4) ?x4))]
      => (* First we assert that we are in one of these cases *)
        remember (max (max head 0) (max x1 (max (head + x4) x4))) as M eqn:EqM;
        assert (M_CASES : M = x1 \/ M = head \/ M = head + x4) by (max_equiv_tac; lia);
        clear EqM;
        (* Them we split up into these cases *)
        destruct_ors M_CASES;
        subst
    end.
    + (* CASE M = x1 *)
      exists n'; exists l'; split; mauto.
    + (* CASE M = h *)
      exists 1%nat; exists (h [::] nil_arr); split; mauto; simpl; mauto.
    + (* CASE M = h + x4 *)
      specialize Hleft as [n'' [l'' [Hprefix Hsum]]];
        destruct_tuple_eqs; subst;
          exists (S n''); exists (h [::] l''); split; mauto.
Qed.

Theorem mss_bound {n1 n2 : nat}:
  forall (l1 : [|n1|]Z) (l2 : [|n2|]Z), Segment n1 n2 l1 l2 -> sum l1 <= mss l2.
Proof.
  intros l1 l2 HSeg;
    induction HSeg as [n1 n2 l1 l2 HPre| ].
  * assert (lem :  let '(x1, x2, x3, x4) := proj1_sig (mss_core l2) in sum l1 <= x2). {
      induction HPre; mauto; solve_for_mss_cores.
    }
    unfold mss;
    mauto; solve_for_mss_cores.
  * apply (Z.le_trans _ (mss l2)); mauto; apply Z.le_refl.
Qed.
Hint Resolve mss_bound : mss.

Theorem mss_attain:
  forall (n2 : nat) (l2 : [|n2|]Z), exists (n1 : nat) (l1 : [|n1|]Z) (pf : Segment n1 n2 l1 l2), sum l1 = mss l2.
Proof.
  intros n2 l2;
  pose proof (mss_core_inner l2) as H;
  unfold mss;
  destruct_mss_core l2;
  specialize H as [n1 [l1 [HSeg Hsum]]];
  subst;
  exists n1; exists l1; exists HSeg;
  reflexivity.
Qed.
