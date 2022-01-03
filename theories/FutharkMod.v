From Coq Require Import List.
From Coq Require Import String.

From ConCert.Extraction Require Import Common.

Import ListNotations.

Require Import FutharkUtils.
Require Import FutharkArrays.

Open Scope bool_scope.
Open Scope arr_scope.

Module Type FutharkSpec.

  Global Create HintDb futhark.

  Parameter map:
    forall {A B : Type} `{Dec A} `{Dec B} {n : nat}
      (f : A -> B) (xs : [|n|]A), [|n|]B.

  Parameter reduce:
    forall {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}
      {n : nat} (xs : [|n|]A), A.

  Parameter scan:
    forall {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}
      {n : nat} (xs : [|n|]A), [|n|]A.

  Parameter zip:
    forall {A B : Type} `{Dec A} `{Dec B} {n : nat}
      (a : [|n|]A) (b : [|n|]B), [|n|](A * B).

  Parameter unzip:
    forall {A B : Type} `{Dec A} `{Dec B} {n : nat}
      (l : [|n|](A * B)), ([|n|]A) * ([|n|]B).

  Section map_axioms.

    Context {A B : Type} `{Dec A} `{Dec B} {n : nat} (f : A -> B).

    Axiom map_cons:
      forall (x : A) (xs : [|n|]A), map f (x [::] xs) = f x [::] (map f xs).

  End map_axioms.

  Section reduce_axioms.

    Context {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Axiom reduce_nil:
      forall l : [|0|]A, reduce op ne l = ne.

    Axiom reduce_cons:
      forall (n : nat) (a : A) (l : [|n|]A),
        reduce op ne (a [::] l) = op a (reduce op ne l).

  End reduce_axioms.

  Section scan_axioms.

    Context {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Axiom scan_cons:
      forall (n : nat) (h : A) (t : [|n|]A),
        scan op ne (h [::] t) = h [::] map (op h) (scan op ne t).

  End scan_axioms.

  Section ziping_axioms.

    Context {A B : Type} `{Dec A} `{Dec B} {n : nat}.

    Variable x : A.
    Variable y : B.

    Axiom zip_cons:
      forall (xs : [|n|]A) (ys : [|n|]B),
        zip (x [::] xs) (y [::] ys) = (x, y) [::] zip xs ys.

    Axiom unzip_cons:
      forall (es : [|n|](A * B)),
        let '(xs, ys) := unzip es in
        unzip ((x, y) [::] es) = (x [::] xs, y [::] ys).

  End ziping_axioms.

  Hint Rewrite @map_cons    using (exact _) : futhark.
  Hint Rewrite @reduce_nil  using (exact _) : futhark.
  Hint Rewrite @reduce_cons using (exact _) : futhark.
  Hint Rewrite @scan_cons   using (exact _) : futhark.
  Hint Rewrite @zip_cons    using (exact _) : futhark.

End FutharkSpec.

Module FutharkMod (F : FutharkSpec).

  Include F.

  Open Scope string.
  Definition prelude_futhark :=
    fold_right (fun x y => x ++ (String (Ascii.ascii_of_nat 10) "") ++ y) ""
      [ "let map_wrapper    [n] 'a 'x (m: i64) (f: a -> x) (as: [n]a) : *[n]x        = map f as"
      ; "let reduce_wrapper [n] 'a    (op: a -> a -> a) (ne: a) (m: i64) (as: [n]a) : a     = reduce op ne as"
      ; "let scan_wrapper   [n] 'a    (op: a -> a -> a) (ne: a) (m: i64) (as: [n]a) : *[n]a = scan op ne as"
      ; "let zip_wrapper    [n] 'a 'b (m: i64) (as: [n]a) (bs: [n]b)  : [n](a, b)    = zip as bs"
      ; "let unzip_wrapper  [n] 'a 'b (m: i64) (xs: [n](a, b))        : ([n]a, [n]b) = unzip xs"
      ].
  Close Scope string.

  Hint Rewrite @munit_left       using (exact _) : futhark.
  Hint Rewrite @munit_right      using (exact _) : futhark.
  Hint Rewrite <- @massoc         using (exact _) : futhark.

  Hint Rewrite @app_nil          using (exact _) : futhark.
  Hint Rewrite @cons_app_assoc   using (exact _) : futhark.
  Hint Rewrite @cons_convert     using (exact _) : futhark.
  Hint Rewrite @cons_convert_sig using (exact _) : futhark.

  Hint Constructors Index : futhark.
  Hint Constructors Prefix : futhark.
  Hint Constructors Segment : futhark.

  Ltac fauto :=
    repeat progress (autorewrite with futhark; auto with futhark).

  Section map.

    Context {A B : Type} `{Dec A} `{Dec B} (f : A -> B).

    Lemma map_nil:
      forall (xs : [|0|]A), map f xs = nil_arr.
    Proof.
      intros xs;
        apply subset_eq;
        destruct (map f xs) as [[]];
        reflexivity + discriminate.
    Qed.
    Hint Rewrite map_nil : futhark.

    Lemma map_app {n1 n2 : nat}:
      forall (xs1 : [|n1|]A) (xs2 : [|n2|]A),
        map f (xs1 [++] xs2) = map f xs1 [++] map f xs2.
    Proof.
      intros xs1;
        induction n1, xs1 as [ |? ? ? IH] using arr_ind;
        intros;
        fauto;
        (* We need [simpl] to replace [(S n1) + n2] with [S (n1 + n2)] in order
           to be able to apply [cons_app_assoc] (via [fauto]). *)
        simpl;
        rewrite <- IH;
        fauto.
    Qed.

    Lemma map_index:
      forall (i n : nat) (a : A) (xs : [|n|]A),
        Index i a xs -> Index i (f a) (map f xs).
    Proof.
      induction 1; fauto.
    Qed.

    Lemma map_prefix:
      forall (i n : nat) (p : [|i|]A) (xs : [|n|]A),
        Prefix p xs -> Prefix (map f p) (map f xs).
    Proof.
      induction 1; fauto.
    Qed.

  End map.

  Hint Rewrite @map_nil : futhark.
  Hint Rewrite @map_app : futhark.
  Hint Resolve map_index : futhark.
  Hint Resolve map_prefix : futhark.

  Section monoid.

    Context {A : Type} `{Dec A} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Theorem reduce_app {n1 n2 : nat}:
    forall (a1 : [|n1|]A) (a2 : [|n2|]A),
      reduce op ne (a1 [++] a2) = op (reduce op ne a1) (reduce op ne a2).
    Proof.
      intros a1 a2;
        induction n1, a1 as [ | n1 a a1 IH] using arr_ind;
        fauto;
        (* We need [simpl] to replace [(S n1) + n2] with [S (n1 + n2)] in order
           to be able to apply [cons_app_assoc] (via [fauto]). *)
        simpl;
        fauto;
        rewrite IH;
        rewrite <- massoc;
        reflexivity.
    Qed.

    Lemma reduce_cons_nil:
      forall (a : A) (l : [|0|]A), reduce op ne (a [::] l) = a.
    Proof.
      intros; fauto.
    Qed.

    Lemma scan_nil:
      forall l : [|0|]A, scan op ne l = nil_arr.
    Proof.
      intros; remember (scan op ne _) as xs; simplify_arrays; reflexivity.
    Qed.

    Theorem scan_index {i n : nat}:
      forall (p : [|S i|]A) (xs : [|n|]A),
        Prefix p xs -> Index i (reduce op ne p) (scan op ne xs).
    Proof.
      intros p;
        generalize dependent n;
        induction i, p using arr_ind_S;
        inversion 1;
        subst_arrs;
        subst;
        fauto.
    Qed.

    Corollary scan_last:
      forall (n : nat) (xs : [|S n|]A), Index n (reduce op ne xs) (scan op ne xs).
    Proof.
      intros n xs; apply scan_index; induction n, xs using arr_ind_S; auto with futhark.
    Qed.

  End monoid.

  Hint Rewrite reduce_cons_nil using (exact _) : futhark.
  Hint Rewrite reduce_app      using (exact _) : futhark.
  Hint Rewrite @scan_nil       using (exact _) : futhark.

  Hint Resolve scan_index : futhark.
  Hint Resolve scan_last  : futhark.

  Section segm_scan.

    Context {A : Type} `{Dec A}.
    Context (op : A -> A -> A) (ne : A).
    Context `{IsMonoid A op ne}.

    Definition segm_scan_op (xp : bool * A) (yp : bool * A) : bool * A :=
      let (x_flag, x) := xp in
      let (y_flag, y) := yp in
      (x_flag || y_flag, if y_flag then y else op x y).

    #[refine]
    Instance segm_scan_monoid : IsMonoid (bool * A) segm_scan_op (false, ne) :=
      {| munit_left  := fun m => _;
        munit_right := fun m => _;
        massoc      := fun m1 m2 m3 => _
      |}.
    all:
      intros;
      repeat (let xp := fresh in
              let b  := fresh in
              match goal with
              | xp : (bool * ?A) |- _ => destruct xp as [[] ?]
              | |- (?b, _) = (?b, _) => f_equal
              end;
              simpl;
              trivial);
      (apply munit_left + apply munit_right + apply massoc).
    Defined.

    (* [Dec (bool * A)] is automatically resolved. *)
    Definition segm_scan {n : nat} (flags : [|n|]bool) (a : [|n|]A) : [|n|]A :=
      let zp := zip flags a in
      snd (unzip (scan segm_scan_op (false, ne) zp)).

    End segm_scan.

End FutharkMod.
