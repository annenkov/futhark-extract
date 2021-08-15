(** Based on [CameLIGOExtract] *)
From Coq Require Import PeanoNat ZArith.
From Coq Require Import List Ascii String.


From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import Kernames.

From ConCert.Extraction Require Import Common ExAst Erasure
     Optimize Extraction TypeAnnotations Annotations Utils ResultMonad.

From Futhark Require Import FutharkPretty.

Local Open Scope string_scope.

Definition futhark_args :=
  {| optimize_prop_discr := true;
     extract_transforms := [Optimize.dearg_transform
                              (fun _ => None)
                              true
                              false (* cannot have partially applied ctors *)
                              true
                              true
                              true] |}.

Import PCUICAst PCUICTyping.
Definition annot_extract_env_cameligo
           (Σ : PCUICAst.global_env)
           (wfΣ : ∥wf Σ∥)
           (include : KernameSet.t)
           (ignore : kername -> bool) : option (∑ Σ, env_annots box_type Σ).
Proof.
  unshelve epose proof (annot_extract_pcuic_env futhark_args Σ wfΣ include ignore _).
  - constructor; [|constructor].
    apply annot_dearg_transform.
  - destruct extract_pcuic_env; [|exact None].
    exact (Some (t; X)).
Defined.


Definition annot_extract_template_env_specalize
           (e : TemplateEnvironment.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result (∑ e, env_annots box_type e) string :=
  let e := SafeTemplateChecker.fix_global_env_universes e in
  let e := TemplateToPCUIC.trans_global_decls e in
  wfe <-check_wf_env_func extract_within_coq e;;
  match annot_extract_env_cameligo e wfe seeds ignore with
  | Some s => Ok s
  | None => Err "failed internally in annot_extract_template_env_specalize"
  end.


Record FutharkTest :=
  { FTname : string;
    FTinput : string;
    FToutput : string }.

Definition print_test (ft : FutharkTest) : string :=
  "-- " ++ ft.(FTname)
  ++ nl
  ++ "-- =="
  ++ nl
  ++ "--" ++ "input { " ++ ft.(FTinput) ++ " }"
  ++ nl
  ++ "-- " ++ "output { " ++ ft.(FToutput) ++ " }"
  ++ nl ++ nl.

Definition printFutharkDefs (prefix : string) (Σ : TemplateEnvironment.global_env)
           (TT : MyEnv.env string)
           (ignore : list kername)
           (test : option FutharkTest)
           (prelude : string)
           (main : kername)
           (extra : list kername)
  : string + string :=
  let seeds := kername_set_of_list (main :: extra) in
  match annot_extract_template_env_specalize Σ seeds (fun k => List.existsb (eq_kername k) ignore) with
  | Ok (eΣ; annots) =>
    (* dependencies should be printed before the dependent definitions *)
    let ldef_list := List.rev (print_global_env prefix TT eΣ annots) in
    (* filtering empty strings corresponding to the ignored definitions *)
    let not_empty_str := (negb ∘ (String.eqb "") ∘ snd) in

    let ldef_ty_list :=
        ldef_list
          |> filter (fun d => match d with
                             (* The type of products are handled as a special case,
                                so we filtering it out *)
                            | TyDecl (kn, _) => negb (eq_kername kn <%% prod %%>)
                            | _ => false
                           end)
          |> map (fun d => match d with ConstDecl d' => d' | TyDecl d' => d' end)
          |> filter not_empty_str in
    let ldef_const_list :=
        ldef_list
          |> filter (fun d => match d with
                           | ConstDecl (kn, _) =>
                             negb (eq_kername kn <%% @fst %%> || eq_kername kn <%% @snd %%>)
                           | _ => false
                           end)
          |> map (fun d => match d with ConstDecl d' => d' | TyDecl d' => d' end)
          |> filter not_empty_str in
    let main := ("let main = " ++ main.2)%string in
    let test_string :=  match test with
                       | Some tst => print_test tst
                       | None => ""
                       end in
    let defs : list string :=
        (ldef_ty_list ++ ldef_const_list) |> map snd in
    (test_string ++ prelude ++ nl ++ nl ++ String.concat (nl ++ nl) defs ++ nl ++ nl ++ main)%string |> inl
  | Err e => inr e
  end.

Definition futhark_extraction {A : Type}
           (prefix : string)
           (prelude : string)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (test : option FutharkTest)
           (def : A) : TemplateMonad (string + string) :=
  '(Σ,_) <- tmQuoteRecTransp def false ;;
  nm <- extract_def_name def;;
  let TT_defs := TT_defs in
  let ignore := map fst TT_defs in
  let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  p <- tmEval lazy
             (printFutharkDefs prefix Σ TT ignore test prelude nm []) ;;
  match p with
  | inl s => ret (inl s)
  | inr s => ret (inr s)
  end.
