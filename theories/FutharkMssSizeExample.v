From Futhark Require Import FutharkExtract.
From Futhark Require Import FutharkPretty.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Utils.
From ConCert.Utils Require Import StringExtra.

From Coq Require Import Datatypes.
From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Arith.
From Coq Require Import Floats.
From Coq Require Import Lia.
From Coq Require Import Logic.Eqdep_dec.

From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import monad_utils.

Import MonadNotation.
From stdpp Require base.

Import ListNotations.

(** TODO This dramatically changes how obligations are solved, and I am not
    entirely sure why.*)
Require Import Program.

Open Scope string.
Open Scope pair_scope.
Open Scope bool_scope.

(** Extracts [program] to Futhark, adds a new definition [extracted_name]
    with the extracted program and also prints the program.
    The definition with the extracted program can be used later on
    to redirect to a file, for example. *)
Definition extract_and_print {A}
           (extracted_name : string)
           (prelude : string)
           (translate_constants : list (BasicAst.kername * string))
           (translate_ctors : list (string * string))
           (tests : option FutharkTest)
           (program : A) :=
  res <- futhark_extraction "" prelude translate_constants translate_ctors tests program;;
  match res with
  | inl s => tmDefinition extracted_name s;;
             tmMsg s
  | inr s => tmFail s
  end.

Definition float_zero := S754_zero false.

Definition nat_to_float : nat -> spec_float :=
    fun n => match n with
          | O => float_zero
          | S _ => S754_finite false (Pos.of_nat n) 0
          end.

(** We remap Coq's types to the corresponding Futhark types. *)
(*  All required operations should be remapped as well. *)
Definition TT :=
  [
  (* natural numbers *)
    remap <%% nat %%> "i64"
  ; remap <%% plus %%> "addI64"
  ; remap <%% mult %%> "multI64"

  (* integers *)
  ; remap <%% Z %%> "i64"
  ; remap <%% Z.add %%> "addI64"
  ; remap <%% Z.mul %%> "multI64"

  (* floats *)
  ; remap <%% spec_float %%> "f64"
  ; remap <%% float_zero %%> "0.0"
  ; remap <%% SF64add %%> "addF64"
  ; remap <%% SF64div %%> "divF64"
  ; remap <%% nat_to_float %%> "f64.i64"

  (* integer inequalities *)
  ; remap <%% Z.leb %%> "lebI64"
  ; remap <%% Z.ltb %%> "ltbI64"
  ; remap <%% Z.geb %%> "gebI64"
  ; remap <%% Z.gtb %%> "gtbI64"

  (* bools *)
  ; remap <%% bool %%> "bool"
  (* lists *)
  ; remap <%% list %%> "[]"
  ; remap <%% @List.length %%> "length"
  ; remap <%% List.fold_right %%> "reduce"

   (* subset types *)
  ; remap <%% sig %%> "sig_"
  ; remap <%% @proj1_sig %%> "id"
].

Definition TT_ctors :=
  [ ("O", "0i64")
  ; ("Z0", "0i64")
  ; ("true", "true")
  ; ("false", "false")].

Open Scope list_scope.

Declare Scope arr_scope.

Module Arrays.

  Open Scope arr_scope.

  (** TODO You need to look into whether you should use a type class for
      decidability, as argument passing becomes very tedious otherwise.

      If you do so, you need to corect the following things:
      - places you call the array tactics and give decidability as argument
      - places you use [proof_irrelevance_arrs].
      - places where you use [arr_ind]. *)

  (* Class Dec (A : Type) := *)
  (*   dec : forall x y : A, {x = y} + {x <> y}. *)

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

End Arrays.

Module Futhark.

  Import Arrays.

  Open Scope arr_scope.

  Class IsMonoid (M : Type) (op : M -> M -> M) (e : M) : Prop :=
    { munit_left : forall m, (op e m) = m;
      munit_right : forall m, (op m e) = m;
      massoc : forall m1 m2 m3, op m1 (op m2 m3) = op (op m1 m2) m3
    }.

  Section reduce.

    Context {A : Type} (A_dec : forall x y : A, {x = y} + {x <> y}).
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
        induction n1, a1 as [empty | n1 h1 a1 IH] using (arr_ind A_dec).
      * intros; rewrite reduce_monoid_homo_unit; rewrite (app_nil A_dec); rewrite munit_left; reflexivity.
      * intros; unfold reduce in *; simpl in *; rewrite IH; rewrite massoc; reflexivity.
    Qed.
    Check reduce_cons.

  End reduce.

  Section scan.

    Context {A : Type} {A_dec : forall x y : A, {x = y} + {x <> y}}.
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
      destruct xs; [apply H1 | apply (H0 a xs (#|xs|))]; split; reflexivity.
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
        apply (proof_irrelevance_arr A_dec);
        simpl;
        repeat f_equal;
        apply (proof_irrelevance_arr A_dec);
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
        destruct_arrs A_dec;
        inversion pre;
        subst;
        simplify_arrays A_dec;
        repeat rewrite (list_cons_arr_cons A_dec);
        rewrite scan__cons.
      * rewrite reduce_cons_nil;
        (** TODO The above rewrite leaves a [IsMonoid A op ne] goal, which I do
            not understand how to avoid. I had hoped it would resolve that
            automatically. *)
        [apply IndexHead | assumption].
      * apply IndexTail;
        rewrite reduce_cons;
        apply (index_map A_dec A_dec);
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
        induction m, xs as [ xs | m h xs IH ] using (arr_ind A_dec);
        intros n Eq;
        [discriminate | destruct n as [ | n ]];
        inversion Eq;
        subst;
        apply PrefixHead.
        + apply PrefixEmpty.
        + apply (IH n); reflexivity.
    Qed.

    (** TODO Maybe this should be moved to the Array Module *)
    Lemma arr_cons_eq {n : nat}:
      forall (x1 x2 : A) (xs1 xs2 : [|n|]A), x1 [::] xs1 = x2 [::] xs2 -> x1 = x2 /\ xs1 = xs2.
    Proof.
      intros ? ? [] [] arr_eq;
        apply (f_equal proj1_sig) in arr_eq;
        simpl in arr_eq;
        inversion arr_eq;
        subst;
        split;
        try apply (proof_irrelevance_arr A_dec);
        reflexivity.
    Qed.

  End scan.

  Section segm_scan.

    Context {A : Type} {A_dec : forall x y : A, {x = y} + {x <> y}}.
    Context (op : A -> A -> A) (ne : A).
    Context `{IsMonoid A op ne}.

    Definition segm_scan__op (xp : bool * A) (yp : bool * A) : bool * A :=
      let (x_flag, x) := xp in
      let (y_flag, y) := yp in
      (x_flag || y_flag, if y_flag then y else op x y).

    #[refine]
    Instance segm_scan__monoid : IsMonoid (bool * A) (segm_scan__op) (false, ne) :=
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

    Lemma bool_A_dec:
      forall x y : bool * A, {x = y} + {x <> y}.
    Proof.
      unfold not in *; intros [[] x] [[] y]; specialize (A_dec x y) as [Eq|Eq];
      try (apply left; f_equal; assumption);
      try (apply right; injection 1; auto).
    Qed.

    Definition segm_scan {n : nat} (flags : [|n|]bool) (a : [|n|]A) : [|n|]A :=
      let zp := zip flags a in
      (unzip (scan segm_scan__op zp)).2.

  End segm_scan.

End Futhark.

Module MaximumSegmentSum.
  (** Futhark implementation of maximum segment sum:

    -- Parallel maximum segment sum
    -- ==
    -- input { [1, -2, 3, 4, -1, 5, -6, 1] }
    -- output { 11 }

    let max(x: i32, y: i32): i32 =
      if x > y then x else y

    let redOp(x: (i32,i32,i32,i32))
            (y: (i32,i32,i32,i32)): (i32,i32,i32,i32) =
      let (mssx, misx, mcsx, tsx) = x in
      let (mssy, misy, mcsy, tsy) = y in
      ( max(mssx, max(mssy, mcsx + misy))
      , max(misx, tsx+misy)
      , max(mcsy, mcsx+tsy)
      , tsx + tsy)

    let mapOp (x: i32): (i32,i32,i32,i32) =
      ( max(x,0)
      , max(x,0)
      , max(x,0)
      , x)

    let main(xs: []i32): i32 =
      let (x, _, _, _) =
        reduce redOp (0,0,0,0) (map mapOp xs) in
      x
  *)

  Import Arrays.
  Import Futhark.

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
    forall x y : X, proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros [] [];
      simpl;
      intros;
      subst;
      f_equal;
      apply (UIP_dec Bool.bool_dec).
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
  Defined.
  Check X__unit.

  #[refine]
  Instance X__monoid : @IsMonoid X redOp X__unit :=
    {| munit_left  := _;
       munit_right := _;
       massoc      := _
    |}.
  (* TODO This is really slow. Is it because I do not help [lia] enough? *)  (* goal 8 slow *)
  all:
    intros;
    apply X_proof_irrellevance;
    destruct_Xs;
    max_equiv_tac;
    split_tuple_eq_goal;
    lia.
  Defined.
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
  Defined.
  Check mapOp.

  Definition mss_core {n : nat} (xs : [|n|]Z) : X :=
    reduce redOp X__unit (map mapOp xs).

  Definition mss {n : nat} (xs : [|n|]Z) : Z :=
    let '(x, _, _, _) := proj1_sig (mss_core xs) in
    x.

  Definition mss_prelude :=
    <$
      sig_defs;
      i64_ops
    $>.

  Definition TT_extra :=
    [ remap <%% @reduce %%> "reduce"
    ; remap <%% @map %%> "map"
    ].

  Definition test_input := to_arr [1; -2; 3; 4; -1; 5; -6; 1] eq_refl.
  Definition test_output := 11.

  Example mss_test : mss test_input = test_output. reflexivity. Qed.

  Definition futhark_mss_test :=
    {| FTname := "Maximum segment sum test"
     ; FTinput := string_of_list (fun n => string_of_Z n ++ "i64")%string (proj1_sig test_input)
     ; FToutput := string_of_Z test_output ++ "i64" |}.

  MetaCoq Run (extract_and_print "mss_futhark"
                                 mss_prelude
                                 (TT ++ TT_extra) TT_ctors
                                 (Some futhark_mss_test)
                                 mss).


  (** From this point we prove functional correctness of the [mss] function*)
  Inductive Segment {A : Type} : forall (n1 n2 : nat), ([|n1|]A) -> ([|n2|]A) -> Prop :=
  | SegmentHead : forall (n1 n2 : nat) (l1 : [|n1|]A) (l2 : [|n2|]A),
      Prefix n1 n2 l1 l2 -> Segment n1 n2 l1 l2
  | SegmentInner : forall (n1 n2 : nat) (h : A) (l1 : [|n1|]A) (l2 : [|n2|]A),
      Segment n1 n2 l1 l2 -> Segment n1 (S n2) l1 (h [::] l2).

  (** TODO The types [Segment] and [Prefix] should maybe be moved to the Arrays
  module. *)

  Lemma Tuple_dec {A B : Type}:
    forall (A_dec : forall x y : A, {x = y} + {x <> y})
      (B_dec : forall x y : B, {x = y} + {x <> y}),
      forall x y : B * A, {x = y} + {x <> y}.
  Proof.
    unfold not;
      intros A_dec B_dec [x1 x2] [y1 y2];
      specialize (B_dec x1 y1) as [Eq1 | Eq1];
      specialize (A_dec x2 y2) as [Eq2 | Eq2];
      subst;
      (apply left; reflexivity) + (apply right; inversion 1; auto).
  Qed.

  Lemma Z_dec:
    forall x y : Z, {x = y} + {x <> y}.
  Proof.
    intros;
      unfold not;
      pose proof (Z_dec x y) as [[Eq | Eq] | Eq];
      [apply right | apply right | apply left];
      lia.
  Qed.

  Lemma ZZZZ_dec:
    forall x y : Z * Z * Z * Z, {x = y} + {x <> y}.
  Proof.
    apply (Tuple_dec Z_dec);
    apply (Tuple_dec Z_dec);
    apply (Tuple_dec Z_dec Z_dec).
  Qed.

  Lemma X_dec:
    forall x y : X, {x = y} + {x <> y}.
  Proof.
    unfold not;
    intros [x px] [y py];
      pose proof (ZZZZ_dec x y) as [Eq | Eq].
    * apply left; subst; apply X_proof_irrellevance; reflexivity.
    * apply right; intros H; apply (f_equal proj1_sig) in H; simpl in H; auto.
  Qed.

  #[refine]
  Instance sum__monoid : IsMonoid Z (fun x y => x + y) 0 :=
    {| munit_left  := _;
       munit_right := _;
       massoc      := _
    |}.
  all: lia.
  Defined.

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
    intros l; induction n, l using (arr_ind Z_dec); autorewrite with mss; reflexivity.
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
    intros l; induction n, l using (arr_ind Z_dec); simplify_arrays Z_dec.
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
      induction n, l as [l|n h l IH] using (arr_ind Z_dec);
      simplify_arrays Z_dec.
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
      induction n, arr using (arr_ind A_dec);
      [ apply Cnil | apply Ccons].
  Qed.

  Theorem mss_bound {n1 n2 : nat}:
    forall (l1 : [|n1|]Z) (l2 : [|n2|]Z), Segment n1 n2 l1 l2 -> sum l1 <= mss l2.
  Proof.
    intros l1 l2 HSeg;
      induction HSeg as [n1 n2 l1 l2 HPre| ].
    * assert (lem :  let '(x1, x2, x3, x4) := proj1_sig (mss_core l2) in sum l1 <= x2). {
        induction HPre;
          simplify_arrays Z_dec.
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

End MaximumSegmentSum.

Redirect "./extracted/auto-generated/mss.fut"
         MetaCoq Run (tmMsg MaximumSegmentSum.mss_futhark).
