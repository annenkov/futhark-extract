From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import ZArith.

Class IsMonoid (M : Type) (op : M -> M -> M) (e : M) : Prop :=
  { munit_left  : forall m, (op e m) = m;
    munit_right : forall m, (op m e) = m;
    massoc      : forall m1 m2 m3, op m1 (op m2 m3) = op (op m1 m2) m3
  }.

#[refine]
Instance nat_sum_monoid : IsMonoid nat (fun x y => x + y) 0 :=
  {| munit_left  := _;
     munit_right := _;
     massoc      := _
  |}.
all: lia.
Qed.

#[refine]
Instance nat_mul_monoid : IsMonoid nat (fun x y => x * y) 1 :=
  {| munit_left  := _;
     munit_right := _;
     massoc      := _
  |}.
all: lia.
Qed.

Open Scope Z.

#[refine]
Instance Z_sum_monoid : IsMonoid Z (fun x y => x + y) 0 :=
  {| munit_left  := _;
     munit_right := _;
     massoc      := _
  |}.
all: lia.
Qed.

Close Scope Z.

Class Dec (A : Type) : Prop :=
  { dec : forall x y : A, x = y \/ x <> y }.

#[refine]
Instance Z_dec : Dec Z := { dec := _ }.
repeat decide equality. Qed.

#[refine]
Instance from_dec {A : Type} (d : forall x y : A, {x = y} + {x <> y}) : Dec A :=
  { dec := _ }.
intros x y; specialize (d x y) as []; [left | right]; assumption. Qed.

Instance bool_dec : Dec bool := from_dec Bool.bool_dec.
Instance nat_dec  : Dec nat := from_dec Nat.eq_dec.

#[refine]
Instance list_dec {A : Type} `{Dec A} : Dec (list A) :=
  { dec := _ }.
decide equality; apply dec. Qed.

#[refine]
Instance Tuple_dec {A B : Type} `{Dec A} `{Dec B} : Dec (A * B) :=
  { dec := _ }.
decide equality; apply dec. Qed.

Class SigEq {A : Type} (P : A -> Prop) : Prop :=
  { subset_eq : forall x y : sig P, proj1_sig x = proj1_sig y -> x = y }.

#[refine]
Instance SigEq_dec {A B : Type} `{Dec B} {f g : A -> B} : SigEq (fun x => f x = g x) :=
  { subset_eq := _ }.
intros [x px] [y py]; simpl; intros; subst; f_equal; apply (eq_proofs_unicity dec).
Qed.

#[refine]
Instance sig_dec {A : Type} {P : A -> Prop} `{Dec A} `{SigEq A P} : Dec (sig P) :=
  { dec := _ }.
intros [x px] [y py];
  specialize (dec x y) as [];
  subst.
* left; apply subset_eq; simpl; reflexivity.
* right; unfold not; inversion 1; auto.
Qed.

(** A result that helps in dealing with situations where heterogeneous equality
    might seem needed. Instead of assuming [JMeq_eq] we can prove that, after a
    function application, elements of equal "dependent subset types" are equal *)
Lemma heterog_subset_eq_f {D X Y : Type} {P : D -> X -> Prop}:
    forall (sigeq : forall (d : D), SigEq (P d))
      (f : forall {d : D}, sig (P d) -> Y)
      (d1 d2 : D)
      (x1 : sig (P d1))
      (x2 : sig (P d2)),
    d1 = d2 -> proj1_sig x1 = proj1_sig x2 -> f x1 = f x2.
Proof.
  intros pi * H1 H2; subst; apply subset_eq in H2; subst; reflexivity.
Qed.
