From Coq Require Import Datatypes.
From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import ZArith.

Import ListNotations.
Require Import Program.

Declare Scope arr_scope.
Open Scope arr_scope.
Open Scope list_scope.

(** TODO You need to look into whether you should use a type class for
    decidability, as argument passing becomes very tedious otherwise.

    If you do so, you need to corect the following things:
    - places you call the array tactics and give decidability as argument
    - places you use [proof_irrelevance_arrs].
    - places where you use [arr_ind]. *)

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |") : arr_scope.

Notation "[| n |] A" := ({ xs : list A | #|xs| = n }) (at level 100) : arr_scope.

#[program] Definition nil_arr {A : Type} : [|0|]A :=
  exist (fun xs : list A => #|xs| = 0) [] _.

Program Definition cons {A : Type} {n : nat} (a : A) (l : [|n|]A) : [|S n|]A :=
  a :: l.
Check cons.

Notation "a [::] l" := (cons a l) (at level 60) : arr_scope.

Program Definition append {A : Type} {n1 n2 : nat} (l1 : [|n1|]A) (l2 : [|n2|]A) : [|n1 + n2|]A :=
  l1 ++ l2.
Next Obligation.
  rewrite app_length; trivial.
Defined.
Check append.

Notation "l1 [++] l2" := (append l1 l2) (at level 60) : arr_scope.

Definition to_arr {A : Type} {n : nat} (l : list A) (len : #|l| = n) : [|n|]A :=
  exist (fun xs : list A => #|xs| = n) l len.

Lemma arr_cons {A : Type}:
  forall (n : nat) (arr : [|S n|]A), exists (h : A) (t : [|n|]A), proj1_sig arr = proj1_sig (h [::] t).
Proof.
  intros n;
    induction n as [ | n IH ];
    intros [[ | h t' ] len];
    try discriminate.
  * exists h; exists nil_arr; destruct t' as [ | h' t' ].
      reflexivity.
    discriminate.
  * simpl in len;
    assert (pf : #|t'| = S n) by lia;
      exists h;
      exists (to_arr t' pf);
      reflexivity.
Qed.

Section pi_and_induction.

  Context {A : Type}.
  Context (A_dec : forall x y : A, {x = y} + {x <> y}).

  Lemma list_dec:
    forall (l1 l2 : list A), {l1 = l2} + {l1 <> l2}.
  Proof.
    intros l1;
      induction l1 as [ | h1 t1 IH1 ];
      intros [ | h2 t2 ].
    * apply left; reflexivity.
    * apply right; discriminate.
    * apply right; discriminate.
    * specialize (A_dec h1 h2) as [hEq | hEq];
      unfold not;
      specialize (IH1 t2) as [tEq | tEq];
      subst;
      (apply left; reflexivity) + (apply right; intros H; injection H; trivial).
  Qed.

  Lemma proof_irrelevance_arr:
    forall (n : nat) (l1 l2 : [|n|]A),
      proj1_sig l1 = proj1_sig l2 -> l1 = l2.
  Proof.
    intros n [l1 len1] [l2 len2] H;
    pose proof (list_dec l1 l2) as [].
    * subst; f_equal; apply UIP_dec; apply eq_nat_dec.
    * contradiction.
  Qed.

  Lemma arr_ind:
  forall (P : forall (n : nat) (arr : [|n|]A), Prop),
    (forall (arr : [|0|]A), P 0 arr)
      -> (forall (n : nat) (a : A) (arr : [|n|]A), P n arr -> P (S n) (a [::] arr))
      -> forall (n : nat) (arr : [|n|]A), P n arr.
  Proof.
    intros P bCase iCase n arr; induction n as [ | n IH ].
    * apply bCase.
    * destruct arr as [[ |h t] len__arr].
      + discriminate.
      + simpl in len__arr;
          injection len__arr as len__t;
          specialize (iCase n h (exist (fun xs : list A => #|xs| = n) t len__t));
          replace (exist (fun xs : list A => #|xs| = S n) (h :: t) len__arr)
            with (h [::] exist (fun xs : list A => #|xs| = n) t len__t)
            by (apply proof_irrelevance_arr; reflexivity);
          apply iCase;
          apply IH.
  Qed.

End pi_and_induction.

Ltac destruct_nil_array a :=
  let h := fresh "h" in
  let t := fresh "t" in
  let len := fresh "len" in
  destruct a as [[ | h t ] len]; [ simpl in len | discriminate len ].

(** TODO maybe this should not do what it does, but rather what
    [list_cons_intro_arr_cons] does. However, this creates a problme with the
    order. *)
Ltac destruct_nonnil_array a :=
  let h := fresh "h" in
  let t := fresh "t" in
  let len := fresh "len" in
  destruct a as [[ | h t ] len]; [ discriminate len | simpl in len ].

Ltac simplify_arrays dec :=
  repeat let a1 := fresh "a" in
          let a2 := fresh "a" in
          let k := fresh "k" in
          let T := fresh "T" in
          let H := fresh "H" in
          match goal with
          | a1 : [|0|]_    |- _ => destruct_nil_array a1
          | a1 : [|S ?k|]_ |- _ => destruct_nonnil_array a1
          | a1 : [|?k|]?T, a2 : [|?k|]?T, H : proj1_sig ?a1 = proj1_sig ?a2 |- _
            => apply (proof_irrelevance_arr dec) in H; subst a1
          end.

Ltac destruct_arrs dec :=
  simplify_arrays dec;
  repeat let a := fresh "a" in
          let k := fresh "k" in
          match goal with
          | a : [|?k|]_ |- _
            => destruct k; [ destruct_nil_array a | destruct_nonnil_array a ]
          end.

Section cons_app.

  Context {A : Type}.
  Context (A_dec : forall x y : A, {x = y} + {x <> y}).

  Lemma cons_app_assoc {n1 n2 : nat}:
    forall (h : A) (a1 : [|n1|]A) (a2 : [|n2|]A), (h [::] a1) [++] a2 = h [::] (a1 [++] a2).
  Proof.
    intros h a1 a2;
      apply (proof_irrelevance_arr A_dec);
      destruct_arrs A_dec;
      reflexivity.
  Qed.

  Lemma cons_app_singleton {n : nat}:
    forall (h : A) (t : [|n|]A), h [::] t = to_arr [h] eq_refl [++] t.
  Proof.
    intros; apply (proof_irrelevance_arr A_dec); reflexivity.
  Qed.

  Lemma app_nil:
    forall (l1 : [|0|]A) (n : nat) (l2 : [|n|]A), l1 [++] l2 = l2.
  Proof.
    intros [[]] *; apply (proof_irrelevance_arr A_dec); simpl; (reflexivity + discriminate).
  Qed.

  Lemma list_cons_arr_cons_len {n : nat}:
    forall (h : A) (t : list A), #|h :: t| = S n -> #|t| = n.
  Proof.
    intros * len; inversion len; reflexivity.
  Qed.

  Lemma list_cons_to_arr_cons {n : nat}:
    forall (h : A) (t : list A) (len : #|h :: t| = S n),
      exist (fun xs : list A => #|xs| = S n) (h :: t) len = h [::] (to_arr t (list_cons_arr_cons_len _ _ len)).
  Proof.
    intros; apply (proof_irrelevance_arr A_dec); reflexivity.
  Qed.

  Lemma list_cons_arr_cons:
    forall (n : nat) (h : A) (arr : [|n|]A) (pf : #|h :: `arr| = S n),
      exist (fun xs : list A => #|xs| = S n) (h :: `arr) pf = h [::] arr.
  Proof.
    intros; apply (proof_irrelevance_arr A_dec); reflexivity.
  Qed.

  (** TODO You do not use it yet, but there are several places where you
      should maybe use it, I think. *)
  Lemma lt_S_n: forall n m : nat, S n < S m -> n < m.
  Proof. intros; lia. Qed.

  (** TODO Figure out if you use it. *)
  Lemma nil_app:
    (* forall (n : nat) (l1 : [|n|]A) (l2 : [|0|]A), l1 [++] l2 = l1. *)
    forall (n : nat) (l1 : [|n|]A) (l2 : [|0|]A), proj1_sig (l1 [++] l2) = proj1_sig l1.
  Proof.
    intros n l1 [[]]; simpl; (apply app_nil_r + discriminate).
  Qed.

End cons_app.

Section indexing.

  Context {A : Type}.
  Context (A_dec : forall x y : A, {x = y} + {x <> y}).

  (** TODO You decided to keep a proof of the inequality arround, but do you
      actually need it? If not, get rid of it.
      Okay, you got rid of it, but will you need it later? *)
  Inductive Index : forall (i n : nat) (a : A) (xs : [|n|]A), Prop :=
  | IndexHead : forall (k : nat) (a : A) (t : [|k|]A), Index 0 (S k) a (a [::] t)
  | IndexTail : forall (i k : nat) (a h : A) (t : [|k|]A), Index i k a t -> Index (S i) (S k) a (h [::] t).

  Lemma index_len_rel:
    forall (i n : nat) (x : A) (xs : [|n|]A), Index i n x xs -> i < n.
  Proof.
    intros i n x xs;
      generalize dependent x;
      generalize dependent i;
      induction n, xs using (arr_ind A_dec);
      intros [ | i ] x cond;
      inversion cond;
      simplify_arrays A_dec;
      subst.
    * apply Nat.lt_0_succ.
    * specialize (IHxs i x); apply lt_n_S; auto.
  Qed.

  Inductive Prefix : forall (l n : nat) (p : [|l|]A) (xs : [|n|]A), Prop :=
  | PrefixEmpty : forall (k : nat) (empty : [|0|]A) (xs : [|k|]A), Prefix 0 k empty xs
  | PrefixHead  : forall (h : A) (l k : nat) (p : [|l|]A) (xs : [|k|]A) ,
                      Prefix l k p xs -> Prefix (S l) (S k) (h [::] p) (h [::] xs).

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
    * apply (H0 h t (S #|t|)); auto.
    * apply (H h t i (#|t|)); auto.
  Defined.
  Next Obligation.
    unfold not; split; intros * [? []]; discriminate.
  Defined.
  Next Obligation.
    unfold not; split; intros * [? []]; discriminate.
  Defined.
  Check safe_index.

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
        => replace xs1 with xs2; [apply IH | apply (proof_irrelevance_arr A_dec); reflexivity]
        (* the rest of the cases. *)
      | |- _ => lia + reflexivity
      end.
  Qed.

  Lemma safe_index_equal_arrays:
    forall (i n : nat) (xs1 xs2 : [|n|]A) (pf1 pf2 : i < n),
      proj1_sig xs1 = proj1_sig xs2 -> safe_index i pf1 xs1 = safe_index i pf2 xs2.
  Proof.
    intros i n xs1 xs2 pf1 pf2 cond;
      replace xs2 with xs1 by (apply proof_irrelevance_arr; assumption);
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
      Index i n x xs -> safe_index i pf xs = x.
  Proof.
    intros i n x xs;
      generalize dependent x;
      generalize dependent i;
      induction n, xs using (arr_ind A_dec);
      intros [ | i ] x pf cond;
      inversion cond;
      simplify_arrays A_dec;
      subst.
    * reflexivity.
    * pose proof (safe_index_head i n a xs pf) as [pf' H];
        rewrite H;
        apply IHxs;
        assumption.
  Qed.

End indexing.

Section map.

  Context {A B : Type}.
  Context (A_dec : forall x y : A, {x = y} + {x <> y}).
  Context (B_dec : forall x y : B, {x = y} + {x <> y}).

  Program Definition map {n : nat} (f : A -> B) (l : [|n|]A) : [|n|]B :=
    List.map f l.
  Next Obligation.
    rewrite List.map_length; reflexivity.
  Defined.

  Lemma map_empty:
    forall (f : A -> B) (xs : [|0|]A), map f xs = nil_arr.
  Proof.
    intros; simplify_arrays A_dec; apply (proof_irrelevance_arr B_dec); reflexivity.
  Qed.

  Lemma map_cons {n : nat}:
    forall (f : A -> B) (x : A) (xs : [|n|]A), map f (x [::] xs) = f x [::] map f xs.
  Proof.
    intros; apply (proof_irrelevance_arr B_dec); reflexivity.
  Qed.

  Lemma map_app {n1 n2 : nat}:
    forall (f : A -> B) (xs1 : [|n1|]A) (xs2 : [|n2|]A), map f (xs1 [++] xs2) = map f xs1 [++] map f xs2.
  Proof.
    intros f xs1;
      induction n1, xs1 as [xs1 | n1 h1 t1 IH] using (arr_ind A_dec);
      intros;
      simpl.
    * rewrite map_empty;
        rewrite (app_nil A_dec);
        rewrite (app_nil B_dec);
        reflexivity.
    * rewrite (cons_app_assoc A_dec);
        rewrite 2 map_cons;
        rewrite (cons_app_assoc B_dec);
        f_equal;
        apply IH.
  Qed.

  Lemma index_map:
    forall (f : A -> B) (i n : nat) (a : A) (xs : [|n|]A),
      Index i n a xs -> Index i n (f a) (map f xs).
  Proof.
    intros f i;
      induction i as [ | i IH ];
      intros n a xs cond;
      destruct_arrs A_dec;
      inversion cond;
      subst;
      rewrite (list_cons_arr_cons A_dec) in *;
      rewrite map_cons.
    * apply IndexHead.
    * apply IndexTail; apply IH; assumption.
  Qed.

  Lemma prefix_map:
    forall (f : A -> B) (l n : nat) (p : [|l|]A) (xs : [|n|]A),
      Prefix l n p xs -> Prefix l n (map f p) (map f xs).
  Proof.
    intros f l;
      induction l as [ | l IH ];
      intros [ | n] p xs cond;
      destruct_arrs A_dec;
      inversion cond;
      simplify_arrays A_dec;
      subst;
      try (apply PrefixEmpty);
      rewrite 2 (list_cons_arr_cons A_dec);
      rewrite 2 map_cons;
      apply PrefixHead;
      apply IH;
      assumption.
  Qed.

End map.

Section ziping.

  Context {A B : Type}.
  Context (A_dec : forall x y : A, {x = y} + {x <> y}).
  Context (B_dec : forall x y : B, {x = y} + {x <> y}).

  Program Fixpoint unzip {n : nat} (l : [|n|](A * B)) : ([|n|]A) * ([|n|]B) :=
    split l.
  Solve Obligations with (intros n [];
                        simpl;
                        (rewrite split_length_l + rewrite split_length_r);
                        assumption).
  Check unzip.

  #[local] Obligation Tactic := try now program_simpl.

  Program Fixpoint zip {n : nat} (a : [|n|]A) (b : [|n|]B) : [|n|](A * B) :=
    combine a b.
  Next Obligation.
    intros n [? len1] [? len2];
      simpl;
      rewrite combine_length;
      rewrite len1;
      rewrite len2;
      lia.
  Defined.
  Check zip.

End ziping.

  (** TODO Here you match on decidability, which you would rather not, Also,
      it might not be the right location for it, and it is doing the same as
      the one above, but better. *)
  (** TODO You can also match were ?t is not a list, but already the
      projection of an array, and then apply the result directly, or when it
      is a complex expression, and then you just remember it first. *)
  (** TODO Also, maybe this should not be necessary if you have used induction
      principles and such properly. *)
  Ltac list_cons_intro_arr_cons :=
    repeat (let T := fresh "T" in
            let n := fresh "n" in
            let h := fresh "h" in
            let t := fresh "t" in
            let dec := fresh "dec" in
            let x := fresh "x" in
            let y := fresh "y" in
            let xs := fresh "xs" in
            let len := fresh "len" in
            let a := fresh "a" in
            let Eq := fresh "Eq" in
            match goal with
            | dec : forall x y : ?T, {x = y} + {x <> y}
                                |- context[exist (fun xs : list ?T => #|xs| = S ?n) (?h :: ?t) ?len]
              => remember (exist (fun xs : list T => #|xs| = S n) (h :: t) len) as a eqn:Eq;
                rewrite (list_cons_to_arr_cons dec) in Eq;
                subst a
            end).
