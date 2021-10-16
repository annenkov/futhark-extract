From Coq Require Import List.

Import ListNotations.

Require Import FutharkUtils.

Module Type FutharkSpec.

  Global Create HintDb futhark.

  Parameter map:
    forall {A B : Type} (f : A -> B) (xs : list A), list B.

  Parameter reduce:
    forall {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}
      (xs : list A), A.

  Parameter scan:
    forall {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}
      (xs : list A), list A.

  Section map_axioms.

    Context {A B : Type} (f : A -> B).

    Axiom map_nil:
      map f [] = [].

    Axiom map_cons:
      forall (x : A) (xs : list A), map f (x :: xs) = f x :: (map f xs).

  End map_axioms.

  Section reduce_axioms.

    Context {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Axiom reduce_monoid_homo_unit:
      reduce op ne [] = ne.

    Axiom reduce_cons:
      forall (a : A) (l : list A), reduce op ne (a :: l) = op a (reduce op ne l).

  End reduce_axioms.

  Section scan_axioms.

    Context {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Axiom scan_cons:
      forall (h : A) (t : list A), scan op ne (h :: t) = h :: map (op h) (scan op ne t).

    Axiom scan_nil:
      scan op ne [] = [].

  End scan_axioms.

  Hint Rewrite @map_nil                 using (exact _) : futhark.
  Hint Rewrite @map_cons                using (exact _) : futhark.
  Hint Rewrite @reduce_monoid_homo_unit using (exact _) : futhark.
  Hint Rewrite @reduce_cons             using (exact _) : futhark.
  Hint Rewrite @scan_cons               using (exact _) : futhark.
  Hint Rewrite @scan_nil                using (exact _) : futhark.

End FutharkSpec.

Module FutharkMod (F : FutharkSpec).

  Include F.

  Hint Rewrite @munit_left       using (exact _) : futhark.
  Hint Rewrite @munit_right      using (exact _) : futhark.
  Hint Rewrite <- @massoc         using (exact _) : futhark.

  Hint Rewrite app_nil_r : futhark.
  Hint Rewrite app_nil_l : futhark.
  Hint Rewrite <- app_comm_cons : futhark.

  Ltac fauto :=
    repeat progress (autorewrite with futhark; auto with futhark).

  Section map.

    Context {A B : Type} (f : A -> B).

    Theorem map_app:
      forall (xs ys : list A), map f (xs ++ ys) = map f xs ++ map f ys.
    Proof.
      intros xs *; induction xs; fauto; f_equal; assumption.
    Qed.

  End map.

  Hint Rewrite @map_app : futhark.

  Section reduce.

    Context {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Theorem reduce_monoid_homo_mult:
    forall (xs : list A) (ys : list A),
      reduce op ne (xs ++ ys) = op (reduce op ne xs) (reduce op ne ys).
    Proof.
      intros xs ys;
        induction xs as [|x xs IH];
        fauto;
        rewrite IH;
        rewrite massoc;
        reflexivity.
    Qed.

  End reduce.

  Hint Rewrite @reduce_monoid_homo_mult using (exact _) : futhark.

End FutharkMod.

Module FutharkSpecImpl : FutharkSpec.

  Definition map {A B : Type} (f : A -> B) (xs : list A) : list B :=
    List.map f xs.

  Definition reduce {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne} (xs : list A) : A :=
    fold_right op ne xs.

  Fixpoint scan {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne} (xs : list A) : list A :=
    match xs with
    | [] => []
    | y :: ys => y :: map (op y) (scan op ne ys)
    end.

  Section map_obligatons.

    Context {A B : Type} (f : A -> B).

    Theorem map_nil:
      map f [] = [].
    Proof. intros; reflexivity. Qed.

    Theorem map_cons:
      forall (x : A) (xs : list A), map f (x :: xs) = f x :: (map f xs).
    Proof. intros; reflexivity. Qed.

  End map_obligatons.

  Section reduce_obligatons.

    Context {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Theorem reduce_monoid_homo_unit:
      reduce op ne [] = ne.
    Proof. intros; reflexivity. Qed.

    Theorem reduce_cons:
      forall (a : A) (l : list A), reduce op ne (a :: l) = op a (reduce op ne l).
    Proof. intros; reflexivity. Qed.

  End reduce_obligatons.

  Section scan_obligatons.

    Context {A : Type} (op : A -> A -> A) (ne : A) `{IsMonoid A op ne}.

    Theorem scan_nil:
      scan op ne [] = [].
    Proof. intros; reflexivity. Qed.

    Theorem scan_cons:
      forall (h : A) (t : list A), scan op ne (h :: t) = h :: map (op h) (scan op ne t).
    Proof.
    Proof. intros; reflexivity. Qed.

  End scan_obligatons.

  Hint Rewrite @map_cons : futhark.
  Hint Rewrite @reduce_monoid_homo_unit using (exact _) : futhark.
  Hint Rewrite @reduce_cons             using (exact _) : futhark.
  Hint Rewrite @scan_cons               using (exact _) : futhark.
  Hint Rewrite @scan_nil                using (exact _) : futhark.

End FutharkSpecImpl.

Module FutharkImpl := FutharkMod (FutharkSpecImpl).
