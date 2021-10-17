From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import ZArith.

Class IsMonoid (M : Type) (op : M -> M -> M) (e : M) : Prop :=
  { munit_left : forall m, (op e m) = m;
    munit_right : forall m, (op m e) = m;
    massoc : forall m1 m2 m3, op m1 (op m2 m3) = op (op m1 m2) m3
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

Class Dec (A : Type) : Type :=
  { dec : forall x y : A, {x = y} + {x <> y} }.

#[refine]
Instance Z_dec : Dec Z := { dec := _ }.
repeat decide equality. Qed.

Instance from_dec {A : Type} (d : forall x y : A, {x = y} + {x <> y}) : Dec A :=
  { dec := d }.

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

Class PI {A : Type} (P : A -> Prop) : Prop :=
  { proof_irrelevance : forall x y : sig P, proj1_sig x = proj1_sig y -> x = y }.

#[refine]
Instance PI_eq_dec {A B : Type} `{Dec B} {f g : A -> B} : PI (fun x => f x = g x) :=
  { proof_irrelevance := _ }.
intros [x px] [y py]; simpl; intros; subst; f_equal; apply (UIP_dec dec).
Qed.

#[refine]
Instance sig_eq_dec {A : Type} {P : A -> Prop} `{Dec A} `{PI A P} : Dec (sig P) :=
  { dec := _ }.
intros [x px] [y py];
  specialize (dec x y) as [];
  subst.
* apply left; apply proof_irrelevance; simpl; reflexivity.
* apply right; unfold not; inversion 1; auto.
Qed.

Lemma functional_equality_sig {A B C : Type} {P : A -> B -> Prop}:
    forall (pi : forall (a : A), PI (P a))
    (f : forall {a : A}, sig (P a) -> C)
    (a1 a2 : A)
    (b1 : sig (P a1))
    (b2 : sig (P a2)),
    a1 = a2 -> proj1_sig b1 = proj1_sig b2 -> f b1 = f b2.
Proof.
  intros pi * H1 H2; subst; apply proof_irrelevance in H2; subst; reflexivity.
Qed.
