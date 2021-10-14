From Coq Require Import List.

From stdpp Require base.

Require Import Program.

Import ListNotations.

Require Import FutharkArrays.
Require Import FutharkUtils.

Open Scope bool_scope.
Open Scope arr_scope.

Section reduce.

  Context {A : Type} `{Dec A}.
  Context (op : A -> A -> A) (ne : A).
  Context `{IsMonoid A op ne}.

  Program Definition reduce {n : nat} (xs : [|n|]A) : A :=
    fold_right op ne xs.
  Check reduce.

  (** The reduce function preserves the neutral element as a monoid homomorphism *)
  Theorem reduce_monoid_homo_unit:
    forall l : [|0|]A, reduce l  = ne.
  Proof.
    intros [l len]; destruct l; unfold reduce; simpl; reflexivity + discriminate.
  Qed.

  Corollary reduce_cons:
    forall (n : nat) (a : A) (l : [|n|]A), reduce (a [::] l) = op a (reduce l).
  Proof. intros; reflexivity. Qed.

  Corollary reduce_cons_nil:
    forall (a : A) (l : [|0|]A), reduce (a [::] l) = a.
  Proof.
    intros a l; destruct_nil_array l; unfold reduce; simpl; apply munit_right.
  Qed.
  Check reduce_cons_nil.

  Theorem reduce_monoid_homo_mult {n1 n2 : nat} :
    forall (a1 : [|n1|]A) (a2 : [|n2|]A),
      reduce (a1 [++] a2) = op (reduce a1) (reduce a2).
  Proof.
    intros a1;
      (** TODO I have had to explicitly add [A_dec] though I would like it to
          be resolved automatically, since there is a matching assumptions,
          and it otherwise results in a shelved goal. *)
      induction n1, a1 as [empty | n1 h1 a1 IH] using arr_ind.
    * intros; rewrite reduce_monoid_homo_unit; rewrite app_nil; rewrite munit_left; reflexivity.
    * intros; unfold reduce in *; simpl in *; rewrite IH; rewrite massoc; reflexivity.
  Qed.
  Check reduce_cons.

End reduce.

Section scan.

  Context {A : Type} `{Dec A}.
  Context (op : A -> A -> A) (ne : A).
  Context `{IsMonoid A op ne}.

  Program Fixpoint scan {n : nat} (xs : [|n|]A) : [|n|]A :=
    match xs, n with
    | [], 0 => []
    | h :: t, S n' => h :: map (op h) (@scan n' t)
    | _, _ => !
    end.
  Next Obligation.
    simpl; f_equal; rewrite List.map_length; assumption.
  Defined.
  Next Obligation.
    destruct xs; [apply H2 | apply (H1 a xs (#|xs|))]; split; reflexivity.
  Defined.
  Next Obligation.
    unfold not; split; intros * []; discriminate.
  Defined.
  Next Obligation.
    unfold not; split; intros * []; discriminate.
  Defined.
  Check scan.

  Lemma scan__cons:
    forall (n : nat) (h : A) (t : [|n|]A), scan (h [::] t) = h [::] map (op h) (scan t).
  Proof.
    intros;
      apply proof_irrelevance;
      simpl;
      repeat f_equal;
      apply proof_irrelevance;
      reflexivity.
  Qed.

  (* Result showing that [scan] indeed behaves like it is supposd to. *)
  Theorem scan_index:
    forall (i n : nat) (p : [|S i|]A) (xs : [|n|]A),
      Prefix (S i) n p xs -> Index i n (reduce op ne p) (scan xs).
  Proof.
    intros i;
      induction i as [ | i IH ];
      intros n p xs pre;
      destruct_arrs;
      inversion pre;
      subst;
      simplify_arrays;
      repeat rewrite list_cons_arr_cons;
      rewrite scan__cons.
    * rewrite reduce_cons_nil;
      (** TODO The above rewrite leaves a [IsMonoid A op ne] goal, which I do
          not understand how to avoid. I had hoped it would resolve that
          automatically. *)
      [apply IndexHead | assumption].
    * apply IndexTail;
      rewrite reduce_cons;
      apply index_map;
      apply IH;
      assumption.
  Qed.

  Corollary scan_last:
    forall (n : nat) (xs : [|S n|]A), Index n (S n) (reduce op ne xs) (scan xs).
  Proof.
    intros n xs;
      apply scan_index;
      (* We remember S n and jump through some hoops to start induction from 1. *)
      remember (S n) as m eqn:Eq;
      generalize dependent n;
      induction m, xs as [ xs | m h xs IH ] using arr_ind;
      intros n Eq;
      [discriminate | destruct n as [ | n ]];
      inversion Eq;
      subst;
      apply PrefixHead.
      + apply PrefixEmpty.
      + apply (IH n); reflexivity.
  Qed.

End scan.

Section segm_scan.

  Context {A : Type} `{Dec A}.
  Context (op : A -> A -> A) (ne : A).
  Context `{IsMonoid A op ne}.

  Definition segm_scan__op (xp : bool * A) (yp : bool * A) : bool * A :=
    let (x_flag, x) := xp in
    let (y_flag, y) := yp in
    (x_flag || y_flag, if y_flag then y else op x y).

  #[refine]
  Instance segm_scan__monoid : IsMonoid (bool * A) segm_scan__op (false, ne) :=
    {| munit_left  := fun m => _;
       munit_right := fun m => _;
       massoc      := fun m1 m2 m3 => _
    |}.
  all:
    intros;
    repeat (let xp := fresh in
            let b  := fresh in
            match goal with
            | xp : (bool * ?A) |- _ => destruct xp as [b ?]; destruct b
            end);
    simpl;
    trivial;
    match goal with
    | |- (?b, _) = (?b, _) => f_equal
    end;
    (apply munit_left + apply munit_right + apply massoc).
  Defined.
  Check segm_scan__monoid.

  (* [Dec (bool * A)] is automatically resolved. *)
  Definition segm_scan {n : nat} (flags : [|n|]bool) (a : [|n|]A) : [|n|]A :=
    let zp := zip flags a in
    snd (unzip (scan segm_scan__op zp)).

End segm_scan.
