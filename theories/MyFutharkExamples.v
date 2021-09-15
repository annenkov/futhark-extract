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

Module Utils.

  Class IsMonoid (M : Type) (op : M -> M -> M) (e : M) : Prop :=
    { munit_left : forall m, (op e m) = m;
      munit_right : forall m, (op m e) = m;
      massoc : forall m1 m2 m3, op m1 (op m2 m3) = op (op m1 m2) m3
    }.

  Definition reduce {A : Type} (op : A -> A -> A) (e : A) `{IsMonoid A op e} (xs : list A) : A :=
    fold_right op e xs.

  (** The reduce function is multiplicative as a monoid homomorphism. *)
  Theorem reduce_monoid_homo_mult (A : Type) (op : A -> A -> A) (ne : A) `{IsMonoid A op ne} :
    forall l1 l2 : list A, reduce op ne (l1 ++ l2) = op (reduce op ne l1) (reduce op ne l2).
  Proof.
    intros l1 l2; induction l1 as [ |? ? IH]; simpl.
    * rewrite munit_left; trivial.
    * rewrite IH; rewrite massoc; trivial.
  Qed.

  (** From the multiplicative property of reduce, it behaves as follows with the
      cons operation. *)
  Corollary reduce_monoid_homo_cons (A : Type) (op : A -> A -> A) (ne : A) `{IsMonoid A op ne} :
    forall (a : A) (l : list A), reduce op ne (a :: l) = op a (reduce op ne l).
  Proof. intros; reflexivity. Qed.

  (** The reduce function preserves the neutral element as a monoid homomorphism *)
  Theorem reduce_monoid_homo_unit (A : Type) (op : A -> A -> A) (ne : A) `{IsMonoid A op ne} :
    reduce op ne [] = ne.
  Proof. reflexivity. Qed.

End Utils.

Import Utils.

Module Tuples.
  (** Example of how tuples of length greater than two are exported
      when deconstructed with match or let expressions.
   *)

  Definition tmatch (x : Z * Z * Z * Z) :=
    match x with
    | (y, _, _, _) => y
    end.

  Definition tlet (x : Z * Z * Z * Z) :=
    let '(y, _, _, _) := x in y.

  Definition twiceFirst (x : Z * Z * Z * Z) := (tmatch x, tlet x).

  MetaCoq Run (futhark_extraction "" "" TT []
                                  None
                                  twiceFirst).

End Tuples.

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
    forall x y : X, proj1_sig x = proj1_sig y <-> x = y.
  Proof.
    intros [] []; simpl; split; intros;
      match goal with
      | |- exist _ _ _ = exist _ _ _ => subst; f_equal; apply (UIP_dec Bool.bool_dec)
      | H : exist _ _ _ = exist _ _ _ |- _ => inversion H; reflexivity
      end.
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
    intros;
      destruct_Xs;
      unfold P__X;
      unfold X__cond;
      repeat rewrite max_equiv;
      destruct_tuple_eqs;
      subst;
      split_X_cond_goal;
      lia.
  Defined.
  Check redOp.

  Program Definition X__unit : X := (Z0, Z0, Z0, Z0).
  Next Obligation.
    simpl; unfold P__X; unfold X__cond; split_X_cond_goal; reflexivity.
  Defined.
  Check X__unit.

  #[refine]
  Instance X__monoid : @Utils.IsMonoid X redOp X__unit :=
    {| Utils.munit_left  := _;
       Utils.munit_right := _;
       Utils.massoc      := _
    |}.
  (* TODO This is really slow. Is it because I do not help [lia] enough? Goal 8
     is the slow one *)
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

  Definition mss_core (xs : list Z) : X :=
    Utils.reduce redOp X__unit (map mapOp xs).

  Definition mss (xs : list Z) : Z :=
    let '(x, _, _, _) := proj1_sig (mss_core xs) in
    x.

  Definition mss_prelude :=
    <$
      sig_defs;
      i64_ops
    $>.

  Definition TT_extra :=
    [ remap <%% @Utils.reduce %%> "reduce"
    ; remap <%% @map %%> "map"
    ].

  Definition test_input := [1; -2; 3; 4; -1; 5; -6; 1].
  Definition test_output := 11.

  Example mss_test : mss test_input = test_output. reflexivity. Qed.

  Definition futhark_mss_test :=
    {| FTname := "Maximum segment sum test"
     ; FTinput := string_of_list (fun n => string_of_Z n ++ "i64")%string test_input
     ; FToutput := string_of_Z test_output ++ "i64" |}.

  MetaCoq Run (extract_and_print "mss_futhark"
                                 mss_prelude
                                 (TT ++ TT_extra) TT_ctors
                                 (Some futhark_mss_test)
                                 mss).


  (** From this point we prove functional correctness of the [mss] function*)
  Inductive Segment {A : Type} : list A -> list A -> Type :=
  | HeadSegment  : forall seg tail, Segment seg (seg ++ tail)
  | InnerSegment : forall prefix seg lst, Segment seg lst -> Segment seg (prefix ++ lst).

  #[refine]
  Instance sum__monoid : Utils.IsMonoid Z (fun x y => x + y) 0 :=
    {| Utils.munit_left  := _;
       Utils.munit_right := _;
       Utils.massoc      := _
    |}.
  all: lia.
  Defined.

  Definition sum (l : list Z) : Z :=
    Utils.reduce (fun x y => x + y) 0 l.

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
      rewrite map_app; rewrite Utils.reduce_monoid_homo_mult;
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

End MaximumSegmentSum.

Redirect "./extracted/auto-generated/mss.fut"
         MetaCoq Run (tmMsg MaximumSegmentSum.mss_futhark).
