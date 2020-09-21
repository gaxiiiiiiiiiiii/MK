Require Export Infinity.

Definition Irr R A :=
  Rel R /\ forall x, x ∈ A -> ~ <|x,x|> ∈ R.

Definition Tr R A :=
  Rel R /\ 
  forall x y z, x ∈ A /\ y ∈ A /\ z ∈ A /\ 
  <|x,y|> ∈ R /\ <|y,z|> ∈ R -> 
  <|x,z|> ∈ R.

Definition Part R A :=
  Tr R A /\ Irr R A.
  
Definition Con R A :=
  Rel R /\ 
  forall x y, x ∈ A /\ y ∈ A /\ x <> y -> 
  <|x,y|> ∈ R \/ <|y,x|> ∈ R.

Definition Tot R A :=
  Tr R A /\ Irr R A /\ Con R A.
  
Definition We R A :=
    Irr R A /\
    forall Y, Y ⊆ A /\ Y <> ∅ ->
    exists m, m ∈ Y /\ 
    forall y, y ∈ Y /\ y <> m -> <|m,y|> ∈ R /\ ~ <|y,m|> ∈ R.

Theorem se_con R A :
We R A -> Con R A.
Proof.
  intro H.
  induction H.
  inversion H.
  apply (conj H1).
  intros x y H3.
  induction H3 as [xA]; induction H3 as [yA xy].
  pose (Pairing x y) as U.
  assert (U ⊆  A).
    intros i Hi.
    apply pairing in Hi.
    induction Hi.      
    by subst i.
    by subst i.
    by exists U.
  assert (U <> ∅).
    intro.
    assert (x ∈ U).
      apply pairing.
      by exists A.
      by apply or_introl.
    rewrite H4 in H5.
    assert (x_ : M x) by (by exists A).
    case ((empty x x_) H5).
  specialize (H0 U (conj H3 H4)).
  induction H0 as [m].
  induction H0 as [mU].
  apply pairing in mU.
  assert (y <> x).
    intro.
    apply xy.
    by symmetry.
  assert (y ∈ U).
    apply pairing.
    by exists A.
    by apply or_intror.
  assert (x ∈ U).
    apply pairing.
    by exists A.
    by apply or_introl.
  induction mU as [mx | my].
  + subst m.
    specialize (H0 y (conj H6 H5)).
    induction H0.
    by apply or_introl.
  + subst m.
    specialize (H0 x (conj H7 xy)).
    induction H0.
    by apply or_intror.
  + by exists U.
Qed.


  