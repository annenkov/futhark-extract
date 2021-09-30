
From Futhark Require Import FutharkExtract.
From Futhark Require Import FutharkPretty.
From ConCert.Extraction Require Import Common.

From Coq Require Import Datatypes.
From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.

From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import monad_utils.

Import MonadNotation.
From stdpp Require base.

Import ListNotations.

Require Import FutharkSized.
Require Import FutharkArrays.
Require Import MssSizedDefinition.

Open Scope string.

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

   (* subset types *)
  ; remap <%% sig %%> "sig_"
  ; remap <%% @proj1_sig %%> "id"
].

Definition TT_ctors :=
  [ ("O", "0i64")
  ; ("Z0", "0i64")
  ; ("true", "true")
  ; ("false", "false")].

Definition mss_prelude := (sig_defs ++ i64_ops)%string.

(* Definition mss_prelude := *)
(*   <$ *)
(*     sig_defs; *)
(*     i64_ops *)
(*   $>. *)

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

MetaCoq Run (extract_and_print "mss_sized_futhark"
                                mss_prelude
                                (TT ++ TT_extra) TT_ctors
                                (Some futhark_mss_test)
                                mss).

Redirect "./extracted/auto-generated/mss_sized.fut"
         MetaCoq Run (tmMsg mss_sized_futhark).
