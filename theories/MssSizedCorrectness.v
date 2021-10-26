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

Definition sum {n : nat} (l : [|n|]Z) : Z :=
  reduce (fun x y => x + y) 0 l.

Lemma sum_nil:
  forall (l : [|0%nat|]Z), sum l = 0.
Proof.
  intros; unfold sum; mauto.
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

Lemma mss_core_initial {n : nat}:
  forall l : [|n|]Z,
    let '(_, msil, _, _) := proj1_sig (mss_core l) in
    exists (n' : nat) (l' : [|n'|]Z), Prefix l' l /\ sum l' = msil.
Proof.
  intros l; induction n, l as [ |n h t IH] using arr_ind; mauto; simpl.
  * exists 0%nat. exists nil_arr; split; mauto.
  * destruct_mss_core t;
    (* We split up into tree case and solve these separately *)
    match goal with
    | |- context[max (max ?h 0) (?h + ?mis')]
      => (* First we assert that we are in one of these cases *)
        remember (max (max h 0) (h + mis')) as MIS eqn:EqMIS;
        assert (MIS_CASES : MIS = 0 \/ MIS = h \/ MIS = h + mis') by (max_equiv_tac; lia);
        clear EqMIS;
        (* Them we split up into these cases *)
        destruct_ors MIS_CASES;
        subst
    end.
    + (* CASE M = 0 *)
      exists 0%nat; exists nil_arr; split; mauto.
    + (* CASE M = a *)
      exists 1%nat; exists (h [::] nil_arr); split; mauto; simpl; mauto.
    + (* CASE M = a + e3 *)
      specialize IH as [n1 [l1 [Happend Hsum]]];
        subst; exists (S n1); exists (h [::] l1); split; mauto.
Qed.

Lemma mss_core_inner {n : nat}:
  forall l : [|n|]Z,
    let '(mssl, _, _, _) := proj1_sig (mss_core l) in
    exists (n' : nat) (l' : [|n'|]Z), Segment l' l /\ sum l' = mssl.
Proof.
  intros l; induction n, l as [ |n h t IH] using arr_ind; mauto; simpl.
  * exists 0%nat; exists nil_arr; split; mauto.
  * specialize (mss_core_initial t) as Hleft;
    destruct_mss_core t;
    specialize IH as [n' [l' [Hsegment Hsum]]];
    simpl.
    (* We split up into tree case and solve these separately *)
    match goal with
    | |- context[max (max h 0) (max ?mss' (max h 0 + ?mis'))]
      => (* First we assert that we are in one of these cases *)
        remember (max (max h 0) (max mss' (max h 0 + mis'))) as MSS eqn:EqMSS;
        assert (MSS_CASES : MSS = mss' \/ MSS = h \/ MSS = h + mis')
          by (rewrite max_add_right in EqMSS; max_equiv_tac; lia);
        clear EqMSS;
        (* Them we split up into these cases *)
        destruct_ors MSS_CASES;
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
  forall (l1 : [|n1|]Z) (l2 : [|n2|]Z), Segment l1 l2 -> sum l1 <= mss l2.
Proof.
  intros l1 l2 HSeg;
    induction HSeg as [n1 n2 l1 l2 HPre| ].
  * assert (lem :  let '(_, msil, _, _) := proj1_sig (mss_core l2) in sum l1 <= msil). {
      induction HPre; mauto; solve_for_mss_cores.
    }
    unfold mss;
    mauto; solve_for_mss_cores.
  * apply (Z.le_trans _ (mss l2)); mauto; apply Z.le_refl.
Qed.
Hint Resolve mss_bound : mss.

Theorem mss_attain:
  forall (n2 : nat) (l2 : [|n2|]Z), exists (n1 : nat) (l1 : [|n1|]Z),
    Segment l1 l2 /\ sum l1 = mss l2.
Proof.
  intros n2 l2;
  pose proof (mss_core_inner l2) as H;
  unfold mss;
  destruct_mss_core l2;
  specialize H as [n1 [l1 [HSeg Hsum]]];
  subst;
  exists n1; exists l1;
  split;
  [apply HSeg | reflexivity].
Qed.
