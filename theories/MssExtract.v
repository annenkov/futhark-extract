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

Require FutharkArrays.
Require FutharkUnsized.
Require FutharkModImpl.
Require MssUnsizedDefinition.
Require MssSizedDefinition.

Open Scope string.
Open Scope Z.

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
  ; remap <%% Z.leb %%> "leI64"
  ; remap <%% Z.ltb %%> "ltI64"
  ; remap <%% Z.geb %%> "geI64"
  ; remap <%% Z.gtb %%> "gtI64"

  (* bools *)
  ; remap <%% bool %%> "bool"

  (* lists *)
  ; remap <%% list %%> "[]"

   (* subset types *)
  ; remap <%% sig %%> "sig_"
  ; remap <%% @proj1_sig %%> "id"
].

Definition TT_ctors :=
  [ ("O", "0i64")
  ; ("Z0", "0i64")
  ; ("true", "true")
  ; ("false", "false")].

Module Unsized.

  Import FutharkUnsized.
  Import MssUnsizedDefinition.

  Import FutharkImpl.

  Definition mss_prelude := StringExtra.lines [sig_defs; i64_ops].

  Definition TT_extra :=
    [ remap <%% @reduce %%> "reduce"
    ; remap <%% @map %%> "map"
    ; remap <%% @List.length %%> "length"
    ].

  Definition test_input := [1; -2; 3; 4; -1; 5; -6; 1].
  Definition test_output := 11.

  Example mss_test : mss test_input = test_output.
  unfold test_input; unfold mss; unfold mss_core; fauto. Qed.

  Definition futhark_mss_test :=
    {| FTname := "Maximum segment sum test"
     ; FTinput := string_of_list (fun n => string_of_Z n ++ "i64")%string test_input
     ; FToutput := string_of_Z test_output ++ "i64" |}.

  MetaCoq Run (extract_and_print "mss_futhark"
                                  mss_prelude
                                  (TT ++ TT_extra) TT_ctors
                                  (Some futhark_mss_test)
                                  mss).

End Unsized.

Module Sized.

  Import FutharkModImpl.
  Import FutharkArrays.
  Import MssSizedDefinition.

  Import FutharkImpl.

  Definition mss_prelude :=
    StringExtra.lines
      [ sig_defs
      ; i64_ops
      ; prelude_futhark
      ].

  (* TODO It would be nice to have this is the [FutharkMod] Functor definition,
          but then something goes wrong with namespaces. *)
  Definition TT_futhark :=
    [ remap <%% @map %%>         "map_wrapper"
    ; remap <%% @reduce %%>      "reduce_wrapper"
    ; remap <%% @scan %%>        "scan_wrapper"
    ; remap <%% @zip %%>         "zip_wrapper"
    ; remap <%% @unzip %%>       "unzip_wrapper"
    ; remap <%% @List.length %%> "length_wrapper"
    ; remap <%% @to_arr %%>      "id"
    ].

  Definition TT_extra :=
    TT_futhark ++
    [ remap <%% @andb %%>   "andb"
    ; remap <%% @orb %%>    "orb"
    ].

  Definition test_input := [1; -2; 3; 4; -1; 5; -6; 1].
  Definition test_output := 11.

  Example mss_test : mss_wrapper test_input = test_output.
  unfold test_input; unfold mss_wrapper; unfold mss; unfold mss_core;
    repeat (unfold to_arr; simpl; rewrite cons_convert); fauto. Qed.

  Definition futhark_mss_test :=
    {| FTname := "Maximum segment sum test"
     ; FTinput := string_of_list (fun n => string_of_Z n ++ "i64")%string test_input
     ; FToutput := string_of_Z test_output ++ "i64" |}.

  MetaCoq Run (extract_and_print "mss_futhark"
                                  mss_prelude
                                  (TT ++ TT_extra) TT_ctors
                                  (Some futhark_mss_test)
                                  mss_wrapper).

End Sized.

Redirect "./extracted/auto-generated/mss_unsized.fut"
         MetaCoq Run (tmMsg Unsized.mss_futhark).

Redirect "./extracted/auto-generated/mss_sized.fut"
         MetaCoq Run (tmMsg Sized.mss_futhark).
