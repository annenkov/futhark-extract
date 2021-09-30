Class IsMonoid (M : Type) (op : M -> M -> M) (e : M) : Prop :=
  { munit_left : forall m, (op e m) = m;
    munit_right : forall m, (op m e) = m;
    massoc : forall m1 m2 m3, op m1 (op m2 m3) = op (op m1 m2) m3
  }.
