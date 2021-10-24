From Coq Require Import Datatypes.
From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import ZArith.

Import ListNotations.
Require Import Program.

Require Import FutharkUtils.

Declare Scope arr_scope.

Open Scope arr_scope.
Open Scope list_scope.

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |") : arr_scope.

Notation "[| n |] A" := ({ xs : list A | #|xs| = n }) (at level 100) : arr_scope.

Definition nil_arr {A : Type} : [|0|]A := exist _ [] eq_refl.

Program Definition cons {A : Type} {n : nat} (a : A) (l : [|n|]A) : [|S n|]A :=
  a :: l.

Notation "a [::] l" := (cons a l) (at level 60, right associativity) : arr_scope.

Program Definition append {A : Type} {n1 n2 : nat} (l1 : [|n1|]A) (l2 : [|n2|]A) : [|n1 + n2|]A :=
  l1 ++ l2.
Next Obligation.
  rewrite app_length; trivial.
Defined.

Notation "l1 [++] l2" := (append l1 l2) (at level 60, right associativity) : arr_scope.

Definition to_arr {A : Type} {n : nat} (l : list A) (len : #|l| = n) : [|n|]A :=
  exist (fun xs : list A => #|xs| = n) l len.

Instance arr_sigeq {n : nat} {A : Type} : SigEq (fun xs : list A => #|xs| = n) := SigEq_dec.
Instance arr_dec {n : nat} {A : Type} `{Dec A} : Dec ([|n|]A) := sig_dec.

Lemma equal_arr_f:
  forall (A B : Type) (f : forall {k : nat}, ([|k|]A) -> B) (n1 n2 : nat) (x1 : [|n1|]A) (x2 : [|n2|]A),
    n1 = n2 -> proj1_sig x1 = proj1_sig x2 -> f x1 = f x2.
Proof.
  intros; apply heterog_subset_eq_f; trivial; intros; apply arr_sigeq.
Qed.

Section equality.

  Context {A : Type} `{Dec A} {n : nat}.

  Lemma nil_eq:
    forall (xs : [|0|]A), xs = nil_arr.
  Proof.
    intros [[]]; apply subset_eq; discriminate + reflexivity.
  Qed.

  Lemma arr_cons_eq:
    forall (x1 x2 : A) (xs1 xs2 : [|n|]A), x1 [::] xs1 = x2 [::] xs2 -> x1 = x2 /\ xs1 = xs2.
  Proof.
    intros ? ? [] [] arr_eq;
      apply (f_equal (@proj1_sig _ _)) in arr_eq;
      simpl in arr_eq;
      inversion arr_eq;
      subst;
      split;
      try apply subset_eq;
      reflexivity.
  Qed.

End equality.

Section cons_rewrite.

  Context {A : Type} `{Dec A} {n : nat}.

  Lemma cons_convert_sig_len:
    forall (h : A) (t : list A), #|h :: t| = S n -> #|t| = n.
  Proof.
    intros * len; inversion len; reflexivity.
  Qed.

  Lemma cons_convert:
    forall (h : A) (t : list A) (len : #|h :: t| = S n),
      exist (fun xs : list A => #|xs| = S n) (h :: t) len = h [::] (to_arr t (cons_convert_sig_len _ _ len)).
  Proof.
    intros; apply subset_eq; reflexivity.
  Qed.

  Lemma cons_convert_sig:
    forall (h : A) (arr : [|n|]A) (pf : #|h :: `arr| = S n),
      exist (fun xs : list A => #|xs| = S n) (h :: `arr) pf = h [::] arr.
  Proof.
    intros; apply subset_eq; reflexivity.
  Qed.

End cons_rewrite.

Section decons.

  Context {A : Type} `{Dec A}.

End decons.

Ltac subst_arrs :=
  repeat let xs := fresh in
          let H  := fresh in
          match goal with
          | xs : [|_|]_, H : proj1_sig ?xs = proj1_sig _ |- _
            => apply subset_eq in H; subst xs
          | xs : [|_|]_, H : proj1_sig _ = proj1_sig ?xs |- _
            => apply subset_eq in H; subst xs
          end.

Section induction.

  Context {A : Type} `{Dec A}.

  Variable P : forall {n : nat} (arr : [|n|]A), Prop.
  Hypothesis base_case : P nil_arr.
  Hypothesis ind_step  : forall (n : nat) (a : A) (arr : [|n|]A), P arr -> P (a [::] arr).

  Lemma arr_ind:
    forall (n : nat) (arr : [|n|]A), P arr.
  Proof.
    intros n; induction n as [ | n IH ].
    * intros arr; assert (arr = nil_arr) by apply nil_eq; subst; apply base_case.
    * destruct arr as [[ | h t ] ?].
      + discriminate.
      + rewrite cons_convert; apply ind_step; apply IH.
  Qed.

End induction.

Section destruct.

  Context {A : Type} `{Dec A}.

  Variable P : forall {n : nat} (arr : [|n|]A), Prop.
  Hypothesis nil_case  : forall (arr : [|0|]A), P arr.
  Hypothesis cons_case : forall (n : nat) (a : A) (arr : [|n|]A), P (a [::] arr).

  Lemma arr_dest:
    forall (n : nat) (arr : [|n|]A), P arr.
  Proof.
    intros n arr; induction n, arr using arr_ind; auto.
  Qed.

End destruct.

Section decons.

  Context {A : Type} `{Dec A}.

  Lemma arr_decons:
    forall (n : nat) (arr : [|S n|]A), exists (h : A) (t : [|n|]A), arr = h [::] t.
  Proof.
    intros n [[ |h t]].
    * discriminate.
    * rewrite cons_convert;
      remember (to_arr t _) as t';
      exists h; exists t'; reflexivity.
  Qed.

  Variable P : forall {n : nat} (arr : [|S n|]A), Prop.
  Hypothesis decons : forall (n : nat) (a : A) (arr : [|n|]A), P (a [::] arr).

  Lemma decons_dest:
    forall (n : nat) (arr : [|S n|]A), P arr.
  Proof.
    intros n arr; pose proof (arr_decons n arr) as [h [t]]; subst; auto.
  Qed.

End decons.

Section indeuction_S.

  Context {A : Type} `{Dec A}.

  Variable P : forall {n : nat} (arr : [|S n|]A), Prop.
  Hypothesis base_case : forall (a : A), P (a [::] nil_arr).
  Hypothesis ind_step  : forall (a : A) (n : nat) (arr : [|S n|]A), P arr -> P (a [::] arr).

  Lemma arr_ind_S:
    forall (n : nat) (arr : [|S n|]A), P arr.
  Proof.
    intros n arr;
      destruct n, arr as [n h t] using decons_dest;
      generalize dependent h;
      induction n, t using arr_ind;
      intros.
    + apply base_case.
    + apply ind_step; auto.
  Qed.

End indeuction_S.

Ltac simplify_arrays :=
  repeat let a1 := fresh "a" in
         let a2 := fresh "a" in
         let k := fresh "k" in
         let T := fresh "T" in
         let H := fresh "H" in
         match goal with
         | a1 : [|0|]_    |- _ => rewrite (nil_eq a1)
         | a1 : [|S ?k|]_ |- _ => destruct k, a1 using decons_dest
         | a1 : [|?k|]?T, a2 : [|?k|]?T, H : proj1_sig ?a1 = proj1_sig ?a2 |- _
           => apply subset_eq in H; subst a1
         end.

Section cons_app.

  Context {A : Type} `{Dec A}.

  Lemma cons_app_assoc {n1 n2 : nat}:
    forall (h : A) (a1 : [|n1|]A) (a2 : [|n2|]A), (h [::] a1) [++] a2 = h [::] (a1 [++] a2).
  Proof.
    intros h a1 a2;
      apply subset_eq;
      destruct n1, a1 using arr_dest;
      reflexivity.
  Qed.

  Lemma cons_app_singleton {n : nat}:
    forall (h : A) (t : [|n|]A), h [::] t = to_arr [h] eq_refl [++] t.
  Proof.
    intros; apply subset_eq; reflexivity.
  Qed.

  Lemma app_nil:
    forall (l1 : [|0|]A) (n : nat) (l2 : [|n|]A), l1 [++] l2 = l2.
  Proof.
    intros [[]] *; apply subset_eq; simpl; (reflexivity + discriminate).
  Qed.

  Lemma nil_app:
    forall (n : nat) (l1 : [|n|]A) (l2 : [|0|]A), proj1_sig (l1 [++] l2) = proj1_sig l1.
  Proof.
    intros n l1 [[]]; simpl; (apply app_nil_r + discriminate).
  Qed.

End cons_app.

Section indexing.

  Context {A : Type} `{Dec A}.

  Inductive Index : forall {n : nat} (i : nat) (a : A) (xs : [|n|]A), Prop :=
  | IndexHead : forall {k : nat} (a : A) (t : [|k|]A), Index 0 a (a [::] t)
  | IndexTail : forall {k : nat} (i : nat) (a h : A) (t : [|k|]A),
      Index i a t -> Index (S i) a (h [::] t).

  Inductive Prefix : forall {l n : nat} (p : [|l|]A) (xs : [|n|]A), Prop :=
  | PrefixEmpty : forall {k : nat} (xs : [|k|]A), Prefix nil_arr xs
  | PrefixHead  : forall {l k : nat} (h : A) (p : [|l|]A) (xs : [|k|]A),
                      Prefix p xs -> Prefix (h [::] p) (h [::] xs).

  Inductive Segment : forall {n1 n2 : nat}, ([|n1|]A) -> ([|n2|]A) -> Prop :=
  | SegmentHead : forall {n1 n2 : nat} (l1 : [|n1|]A) (l2 : [|n2|]A),
      Prefix l1 l2 -> Segment l1 l2
  | SegmentInner : forall {n1 n2 : nat} (h : A) (l1 : [|n1|]A) (l2 : [|n2|]A),
      Segment l1 l2 -> Segment l1 (h [::] l2).

  Lemma index_len_rel:
    forall (i n : nat) (x : A) (xs : [|n|]A), Index i x xs -> i < n.
  Proof.
    intros i n x xs;
      generalize dependent x;
      generalize dependent i;
      induction n, xs using arr_ind;
      intros [ | i ] x cond;
      inversion cond;
      simplify_arrays;
      subst.
    * apply Nat.lt_0_succ.
    * specialize (IHxs i x); apply lt_n_S; auto.
  Qed.

  #[program] Fixpoint safe_index {n : nat} (i : nat) (pf : i < n) (xs : [|n|]A) : A :=
    match xs, i, n with
    | h :: t, 0, _       => h
    | h :: t, S i', S n' => @safe_index n' i' _ t
    | _, _, _           => !
    end.
  Next Obligation.
    simpl in pf; lia.
  Defined.
  Next Obligation.
    destruct xs as [ | h t ];
      destruct i as [ | i ];
      simpl in *.
    * inversion pf.
    * inversion pf.
    * apply (H1 h t (S #|t|)); auto.
    * apply (H0 h t i (#|t|)); auto.
  Defined.
  Next Obligation.
    unfold not; split; intros * [? []]; discriminate.
  Defined.
  Next Obligation.
    unfold not; split; intros * [? []]; discriminate.
  Defined.

  Lemma safe_index_pi:
    forall (i n : nat) (xs : [|n|]A) (pf1 pf2 : i < n),
      safe_index i pf1 xs = safe_index i pf2 xs.
  Proof.
    intros i n;
      generalize dependent i;
      induction n as [ | n IH ];
      intros [ | i ] [[ | h t ] len] pf1 pf2;
      simpl in *;
      match goal with
        (* the case where we reduce to indexing into the tail. *)
      | |- safe_index i ?_pf1' ?xs1 = safe_index i ?_pf2' ?xs2
        => replace xs1 with xs2; [apply IH | apply subset_eq; reflexivity]
        (* the rest of the cases. *)
      | |- _ => lia + reflexivity
      end.
  Qed.

  Lemma safe_index_equal_arrays:
    forall (i n : nat) (xs1 xs2 : [|n|]A) (pf1 pf2 : i < n),
      proj1_sig xs1 = proj1_sig xs2 -> safe_index i pf1 xs1 = safe_index i pf2 xs2.
  Proof.
    intros i n xs1 xs2 pf1 pf2 cond;
      replace xs2 with xs1 by (apply subset_eq; assumption);
      apply safe_index_pi.
  Qed.

  Lemma safe_index_head:
    forall (i n : nat) (x : A) (xs : [|n|]A) (pf : S i < S n), exists (pf' : i < n),
      safe_index (S i) pf (x [::] xs) = safe_index i pf' xs.
  Proof.
    intros [ | i ] [ | n ] x [[ | h t ] len] pf;
      (* take cara of all cases with contradicting inequalities. *)
      try (simpl in *; lia).
    * (* Cases indexing the head of the list. *)
      exists (Nat.lt_0_succ n); reflexivity.
    * (* Cases indexing the tail of the list. *)
      assert (pf' : S i < S n) by (lia);
        exists pf';
        simpl;
        apply safe_index_equal_arrays;
        reflexivity.
  Qed.

  Lemma safe_index_correct:
    forall (i n : nat) (x : A) (xs : [|n|]A) (pf : i < n),
      Index i x xs -> safe_index i pf xs = x.
  Proof.
    induction 1 as [ | n i x h t HInd IH ].
    + reflexivity.
    + pose proof (safe_index_head i n h t pf) as [pf' Hsafe];
      rewrite Hsafe;
      apply IH.
  Qed.

End indexing.
