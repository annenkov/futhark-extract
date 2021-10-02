From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import ZArith.

Require Import FutharkArrays.
Require Import FutharkUtils.
Require Import FutharkSized.
Require Import MssUtils.
Require Import MssSizedDefinition.

Open Scope Z.

(** TODO The types [Segment] and [Prefix] should maybe be moved to the Arrays
module. *)

(** From this point we prove functional correctness of the [mss] function*)
Inductive Segment {A : Type} : forall (n1 n2 : nat), ([|n1|]A) -> ([|n2|]A) -> Prop :=
| SegmentHead : forall (n1 n2 : nat) (l1 : [|n1|]A) (l2 : [|n2|]A),
    Prefix n1 n2 l1 l2 -> Segment n1 n2 l1 l2
| SegmentInner : forall (n1 n2 : nat) (h : A) (l1 : [|n1|]A) (l2 : [|n2|]A),
    Segment n1 n2 l1 l2 -> Segment n1 (S n2) l1 (h [::] l2).

Definition sum {n : nat} (l : [|n|]Z) : Z :=
  reduce (fun x y => x + y) 0 l.

Lemma sum_cons:
  forall (n : nat) (a : Z) (l : [|n|]Z), sum (a [::] l) = a + sum l.
Proof.
  unfold sum; intros; rewrite reduce_cons; reflexivity.
Qed.
Hint Rewrite sum_cons : mss.

Definition sum_list (l : list Z) : Z :=
  fold_right (fun x y => x + y) 0 l.

Lemma sum_form {n : nat}:
  forall l : [|n|]Z, sum l = sum_list (proj1_sig l).
Proof.
  intros l; induction n, l using arr_ind; autorewrite with mss; reflexivity.
Qed.
Hint Rewrite @sum_form : mss.

Lemma mss_core_cons {n : nat}:
  forall (h : Z) (t : [|n|]Z),
    mss_core (h [::] t) = redOp (mapOp h) (mss_core t).
Proof.
  intros; unfold mss_core; reflexivity.
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
  intros; unfold mss; rewrite mss_core_cons; solve_for_mss_cores.
Qed.

Hint Resolve Z.add_0_r : mss.

Lemma mss_core_left {n : nat}:
  forall l : [|n|]Z,
    let '(_, x2, _, _) := proj1_sig (mss_core l) in
    exists (n' : nat) (l' : [|n'|]Z), Prefix n' n l' l /\ sum l' = x2.
Proof.
  intros l; induction n, l using arr_ind; simplify_arrays.
  * exists 0%nat; exists nil_arr; split; [ apply PrefixEmpty | auto ].
  * autorewrite with mss;
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
      exists 0%nat; exists nil_arr; split.
      - apply PrefixEmpty.
      - auto.
    + (* CASE M = a *)
      exists 1%nat; exists (a [::] nil_arr);
        autorewrite with mss;
        split.
        - apply PrefixHead; apply PrefixEmpty.
        - simpl; auto with mss.
    + (* CASE M = a + e3 *)
      specialize IHl as [n1 [l1 [Happend Hsum]]];
        exists (S n1); exists (a [::] l1); split.
        - apply PrefixHead; apply Happend.
        - rewrite sum_cons; rewrite Hsum; reflexivity.
Qed.

Lemma mss_core_inner {n : nat}:
  forall l : [|n|]Z,
    let '(x1, _, _, _) := proj1_sig (mss_core l) in
    exists (n' : nat) (l' : [|n'|]Z), Segment n' n l' l /\ sum l' = x1.
Proof.
  intros l;
    induction n, l as [l|n h l IH] using arr_ind;
    simplify_arrays.
  * exists 0%nat; exists nil_arr; split.
    - apply SegmentHead; apply PrefixEmpty.
    - auto.
  * specialize (mss_core_left l) as Hleft;
    rewrite mss_core_cons;
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
      exists n'; exists l'; split.
      - apply SegmentInner; assumption.
      - reflexivity.
    + (* CASE M = h *)
      exists 1%nat; exists (h [::] nil_arr); split.
      - apply SegmentHead; apply PrefixHead; apply PrefixEmpty.
      - autorewrite with mss; simpl; auto with mss.
    + (* CASE M = h + x4 *)
      specialize Hleft as [n'' [l'' [Hprefix Hsum]]];
        exists (S n''); exists (h [::] l'');
          split.
      - apply SegmentHead; apply PrefixHead; assumption.
      - rewrite sum_cons; rewrite Hsum; reflexivity.
Qed.

(** TODO this should be moved next to the induction principle. *)
Lemma arr_dest {A : Type} (A_dec : forall x y : A, {x = y} + {x <> y}):
  forall (P : forall (n : nat) (arr : [|n|]A), Prop),
    (forall (arr : [|0%nat|]A), P 0%nat arr)
      -> (forall (n : nat) (a : A) (arr : [|n|]A), P (S n) (a [::] arr))
      -> forall (n : nat) (arr : [|n|]A), P n arr.
Proof.
  intros P Cnil Ccons n arr;
    induction n, arr using arr_ind;
    [ apply Cnil | apply Ccons].
Qed.

Theorem mss_bound {n1 n2 : nat}:
  forall (l1 : [|n1|]Z) (l2 : [|n2|]Z), Segment n1 n2 l1 l2 -> sum l1 <= mss l2.
Proof.
  intros l1 l2 HSeg;
    induction HSeg as [n1 n2 l1 l2 HPre| ].
  * assert (lem :  let '(x1, x2, x3, x4) := proj1_sig (mss_core l2) in sum l1 <= x2). {
      induction HPre;
        simplify_arrays.
      + destruct_mss_cores; autorewrite with mss; simpl; auto with mss.
      + rewrite mss_core_cons;
          rewrite sum_cons;
          solve_for_mss_cores.
    }
    unfold mss;
      solve_for_mss_cores.
  * apply (Z.le_trans _ (mss l2)).
    + assumption.
    + apply mss_cons_r.
Qed.

Theorem mss_attain:
  forall (n2 : nat) (l2 : [|n2|]Z), exists (n1 : nat) (l1 : [|n1|]Z) (pf : Segment n1 n2 l1 l2), sum l1 = mss l2.
Proof.
  intros n2 l2;
  pose proof (mss_core_inner l2) as H;
  unfold mss;
  destruct_mss_core l2;
  specialize H as [n1 [l1 [HSeg Hsum]]];
  subst;
  exists n1;
  exists l1;
  exists HSeg;
  reflexivity.
Qed.
