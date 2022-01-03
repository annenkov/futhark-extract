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

From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import monad_utils.

Import MonadNotation.
From stdpp Require  base.

Import ListNotations.


Open Scope string.
Open Scope pair_scope.

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

(** We remap Coq's types to the corresponding Futhark types.
 All required operations should be remapped as well. *)
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

Open Scope string.

Module PatternMatching.

  Inductive Dec :=
  | Yes (_ : Z)
  | No (_ : Z).

  Definition add_dec (d1 d2 : Dec) : Z :=
    match d1,d2 with
    | Yes i1, Yes i2
    | Yes i1, No i2
    | No i1, Yes i2
    | No i1, No i2  => i1 + i2
    end.

  MetaCoq Run (extract_and_print
                 "add_dec_futhark"
                 i64_ops
                 TT
                 TT_ctors
                 None
                 add_dec).
End PatternMatching.


Module TupleMatch.
  (** Example of how deconstructing tuples with match or let
      expressions work. *)

  Definition tmatch (x : Z * Z * Z * Z) :=
    match x with
    | (y, _, _, _) => y
    end.

  Definition tlet (x : Z * Z * Z * Z) :=
    let '(y, _, _, _) := x in y.

  Definition twiceFirst (x : Z * Z * Z * Z) := (tmatch x, tlet x).

  MetaCoq Run (extract_and_print "tuple_match_futhark" "" TT []
                                  None
                                  twiceFirst).

End TupleMatch.


Module Sum.

  (** A simple example of reduction *)

  Definition sum (xs: list nat) := fold_right plus 0 xs.

  Definition test_input := [4;3;2;1].
  Definition test_output := 10.

  Example sum_test : sum test_input = test_output. reflexivity. Qed.

  Definition futhark_sum_test :=
    {| FTname := "Sum test"
     ; FTinput := string_of_list (fun n => string_of_nat n ++ "i64") test_input
     ; FToutput := string_of_nat test_output ++ "i64" |}.

  MetaCoq Run (extract_and_print "sum_futhark" i64_ops TT TT_ctors
                                  (Some futhark_sum_test)
                                  sum).

End Sum.

Module Average.

  (** An example from the fronpage of https://futhark-lang.org/ *)

  (** We use the [spec_float] type, which is a specification of IEEE754 floating-point numbers in Coq.
   That allows for proving properties related to the precision of operations on floats.*)

  Open Scope float.

  Definition average (xs: list spec_float) : spec_float :=
    SF64div (fold_right SF64add float_zero xs) (nat_to_float (length xs)).


  Example average_test : average (map Prim2SF [10.5; 20.5]) = Prim2SF 15.5.
  Proof. reflexivity. Qed.

  Definition futhark_average_test :=
    {| FTname := "Average test"
     ; FTinput := "[10.5f64,20.5f64]" (* we can't print float literals currently *)
     ; FToutput := "15.5f64" |}.

  MetaCoq Run (extract_and_print "average_futhark" f64_ops TT TT_ctors
                                  (Some futhark_average_test)
                                  average).

End Average.

Module Monoid.
  (** In this example, we provide a "safe" parallel reduction operation.
   It is safe in the sense that it requires an operation and a neutral element of a carrier type to be a monoid *)

  Class IsMonoid (M : Type) (op : M -> M -> M) (e : M) : Prop:=
    { munit_left : forall m, op e m = m;
      munit_right : forall m, op m e = m;
      massoc : forall m1 m2 m3, op m1 (op m2 m3) = op (op m1 m2) m3
    }.

  Definition parallel_reduce {A : Type} (op : A -> A -> A) (e : A) `{IsMonoid A op e} (xs : list A) :=
    fold_right op e xs.

  (** We cannot define [sum], because Coq cannot find appropriate instance *)
  Fail Definition sum (xs : list Z) := parallel_reduce Z.add 0%Z.

  (** So, we define the required instance *)
  #[refine]
  Instance Z_add_monoid : IsMonoid Z Z.add 0%Z :=
    {| munit_left := fun m => _;
       munit_right := _;
       massoc := _
    |}.
  * reflexivity.
  * apply Z.add_0_r.
  * intros;apply Z.add_assoc.
  Defined.

  (** Now, it works as expected *)
  Definition sum (xs : list Z) := parallel_reduce Z.add 0%Z.

  (** We tell our extraction that our parallel reduce is Futhark's reduce *)
  Definition TT_extra :=
    [ remap <%% @parallel_reduce %%> "reduce"].

  (** The witness of the instance [Z_add_monoid] is erased, because it's a proposition.
   So, we are left with an ordinary Futhark function *)
  MetaCoq Run (extract_and_print "sum_futhark" i64_ops (TT ++ TT_extra) TT_ctors
                                  None
                                  sum).
  (* Geneterates the following function: *)
  (* let sum  = reduce addI32 0i32 *)
End Monoid.

Module DotProduct.

  Open Scope Z.

  Definition map2 {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B)
             (p : length xs = length ys) : list C :=
    map (fun '(x,y) => f x y) (combine xs ys).

  Definition TT_extra :=
    [ remap <%% @map2 %%> "map2"
    ; remap <%% List.split %%> "unzip"].

  (** A function computing a dot product of two lists.
   It also takes a proof that the two lists have the same length.
   Eventually, we should be able to use vectors (sized lists) in such functions *)
  Definition dotprod (xs: list Z) (ys: list Z) (p : length xs = length ys):=
    fold_right Z.add 0%Z (map2 Z.mul xs ys p).

  (** The input is a list of pairs, which is basically N x 2 matrix.
   We take a dot product of the two vertical columns.
   We can prove that the sizes of the arguments to [dotprod] are of the same size *)
  Program Definition dotprod_list_of_pairs (xs : list (Z * Z)) :=
    let pair_of_lists := List.split xs in
    dotprod pair_of_lists.1 pair_of_lists.2 _.
  Next Obligation.
    intros. subst pair_of_lists.
    now rewrite split_length_l, split_length_r.
  Defined.

  Definition test_input :=
    [(1, 4)
    ;(2,-5)
    ;(3, 6)].

  Definition test_output := 12.

  Example dotprod_test : dotprod_list_of_pairs test_input = test_output. reflexivity. Qed.

  Definition futhark_dotprod_test :=
    {| FTname := "Dotproduct test"
     ; FTinput := string_of_list
                      (fun '(n,m) => parens false (string_of_Z n ++ "," ++ string_of_Z m)) test_input
     ; FToutput := string_of_Z test_output |}.


  (** Unfortunately, Futhark test syntax doesn't support tuples, so we don't generate the test *)
  MetaCoq Run (extract_and_print "dotprod_list_of_pairs_futhark" i64_ops (TT ++ TT_extra) TT_ctors
                                 None
                                 dotprod_list_of_pairs).

End DotProduct.

Notation "[| n |] A" := ({ xs : list A | #|xs| = n }) (at level 100).

Module RefinementTypes.

  Import Lia.

  Hint Resolve combine_length : core.

  Program Definition zip {A B n} (xs : [|n|]A) (ys : [|n|]B) : [|n|](A*B) :=
    combine xs ys.
  Next Obligation.
    intros;destruct xs,ys;cbn. rewrite combine_length;lia.
  Qed.

  Program Definition concat {A n m} (xs : [|n|]A) (ys : [|m|]A) : [|n+m|]A
    := (xs ++ ys)%list.
  Next Obligation.
    intros;destruct xs,ys;cbn;subst;apply app_length; lia.
  Qed.

  (** In this example we use commutativity of addition to type check the definition *)
  Program Definition zip_concat_swap {n m} (xs : [|n|]Z) (ys : [|m|]Z)
    : [| m+n |] (Z * Z) :=
    zip (concat xs ys) (concat ys xs).
  Next Obligation.
    cbn;intros. destruct xs,ys;cbn;subst. rewrite app_length; lia.
  Qed.
  Next Obligation.
    intros. destruct xs,ys;cbn;subst.
    rewrite combine_length; repeat rewrite app_length. lia.
  Qed.

  Program Definition zip_self {n} (xs : {l : list Z | length l = n}) : {l | length l = n } := zip xs xs.

  Definition TT_extra :=
    [ remap <%% @zip %%> "zip"
    ; remap <%% @concat %%> "concat"
    ].

  (** The statement below produces "almost compilable" code :)
     It requires some type coercions to be inserted in order to compile *)
  MetaCoq Run (extract_and_print "zip_concat_swap_futhark" sig_defs
                                 (TT ++ TT_extra)
                                 TT_ctors
                                 None
                                 zip_concat_swap).
End RefinementTypes.

Module Indexing.

  Import Lia.

  Program Definition safe_index {A} : forall (l : list A), {n : nat | n < List.length l} -> A :=
    fix go (l : list A) (n : nat | n < List.length l) : A :=
      match l with
      | nil => _
      | hd :: tl =>
        match n with
        | 0 => hd
        | S n => go tl n
        end
      end.
  Next Obligation.
  intros;subst;cbn in *. destruct n as [n Hn]. exfalso;inversion Hn.
  Defined.
  Next Obligation.
    intros. subst;simpl in *. destruct n0 as [n1 Hn1].
    subst filtered_var. cbn in *. subst. auto with arith.
  Defined.

  Fixpoint repl_iota_aux (i : nat) (xs : list nat) : list nat :=
    match xs with
    | [] => []
    | x :: xs' => repeat i x ++ repl_iota_aux (1+i) xs'
    end.

  Definition repl_iota := repl_iota_aux 0.

  Example repl_iota_1 : repl_iota [2;3;1] = [0;0;1;1;1;2].
  Proof. reflexivity. Qed.

  Example repl_iota_2 : repl_iota [1;2;3] = [0;1;1;2;2;2].
  Proof. reflexivity. Qed.

  Lemma repl_iota_aux_decompose n i a l :
    In i (repeat n a ++ repl_iota_aux (1+n) l) ->
    i = n \/ In i (repl_iota_aux (1+n) l).
  Proof.
    intros H.
    apply Erasure.In_app_inv in H.
    destruct H.
    - apply repeat_spec in H;auto.
    - auto.
  Qed.

  Lemma repl_iota_aux_lt {n i xs} :
    In i (repl_iota_aux n xs) ->
    i < n + #|xs|.
  Proof.
    revert dependent i.
    revert dependent n.
    induction xs;intros n i H.
    - inversion H.
    - cbn in *.
      apply repl_iota_aux_decompose in H.
      destruct H.
      * lia.
      * replace (n + S #|xs|) with (S n + #|xs|) by lia.
        apply IHxs;auto.
  Qed.

  Program Definition repl_iota_rt {n} (xs : [|n|]nat) :
    {l : list nat | forall i, In i l -> i < n } :=
    repl_iota xs.
  Next Obligation.
    cbn;intros n xs i H.
    destruct xs as [l Hsize];cbn in *. subst.
    apply @repl_iota_aux_lt with (n:=0);auto.
  Qed.

  (** The implementation is a bit tricky, because while we map through [idxs]
      we need to know that each element is actually coming from [idxs].
      If we use the standard [map], this information is lost.
      For that reason we use [map_In], which takes a function of two arguments:
      an element of a list and a proof that this element is in the list passed to [map_In] as an argument *)
  Program Definition segm_replicate {n} (reps : [|n|]nat) (vs : [|n|]nat)
    : list nat :=
    let idxs := repl_iota_rt reps in
    map_In idxs (fun i Hin => safe_index vs i).

  Next Obligation.
    intros. cbn.
    destruct idxs as [l Hl];cbn in *.
    destruct vs;cbn in *; subst;auto.
  Qed.

  Definition prelude_extra :=
     "import ""../lib/repl_iota""" ++ nl ++(* we treat [repl_iota] as a library function *)
      "" ++ nl ++
      "let unsafe_index 'a (xs : []a) (i: i64) : a = #[unsafe] xs[i]" ++ nl ++
        (* we also need a wrapper around our [map_In] function, since it's signature differs from the Futhark's [map] *)
      "let map_wrapper 'a 'b (xs : []a) (f : a -> () -> b) : []b = map (\x -> f x ()) xs".

  Definition TT_extra :=
    [ remap <%% @Utils.map_In %%> "map_wrapper"
    ; remap <%% @repl_iota_rt %%> "repl_iota"
    ; remap <%% @safe_index %%> "unsafe_index"
    ].

  (* NOTE: Clearly, using [segm_replicate] as a "library" function is not safe,
     because the invariant that the two arrays are of the same size is erased
     and curretnly we don't generate explicit sizes for the array types.
     However, it could be called from a wrapper that ensures the required
     preconditions hold. *)
  MetaCoq Run (extract_and_print "segm_replicate_futhark"
                                     (prelude_extra ++ nl ++ sig_defs)
                                     (TT ++ TT_extra)
                                     TT_ctors
                                     None
                                     segm_replicate).
End Indexing.

(** Here, we redirect the previuosly extracted programs to files *)
(** This part cannot be evaluated in the interactive mode, because one has to provide fixed paths. Therefore, we use path from the project's root, so it works when building the project using [makefile] *)

(* NOTE: we use [MetaCoq Run (tmMsg ...)] instead of [Print], because
   [Print] adds some extra stuff, which we don't need *)

Redirect "./extracted/auto-generated/pattern_matching.fut"
         MetaCoq Run (tmMsg PatternMatching.add_dec_futhark).

Redirect "./extracted/auto-generated/tuple_match.fut"
         MetaCoq Run (tmMsg TupleMatch.tuple_match_futhark).

Redirect "./extracted/auto-generated/average.fut"
         MetaCoq Run (tmMsg Average.average_futhark).

Redirect "./extracted/auto-generated/monoid.fut"
         MetaCoq Run (tmMsg Monoid.sum_futhark).

Redirect "./extracted/auto-generated/dot_product.fut"
         MetaCoq Run (tmMsg DotProduct.dotprod_list_of_pairs_futhark).

(* NOTE: this example is currently does not compile without some manual editing.
   It requres a type coercion, which we cannot insert automatically yet. *)
(* Redirect "./extracted/auto-generated/refinement_types.fut" *)
(*          MetaCoq Run (tmMsg RefinementTypes.zip_concat_swap_futhark). *)

Redirect "./extracted/auto-generated/segm_replicate.fut"
         MetaCoq Run (tmMsg Indexing.segm_replicate_futhark).
