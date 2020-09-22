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

Theorem we_con {R A} :
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

Theorem we_tr {R A} : 
  We R A -> Tr R A.
Proof.
  intro H.
  inversion H.
  inversion H0.
  apply (conj H2).
  intros x y z H4.
  induction H4 as [xA]; induction H4 as [yA]; induction H4 as [zA].
  induction H4 as [xy yz].
  pose ({: A | fun i => i = x \/ i = y \/ i = z:}) as U.
  assert (xU : x ∈ U).
    apply separation.
    apply (conj xA).
    by apply or_introl.
 assert (yU : y ∈ U).
    apply separation.
    apply (conj yA).
    apply or_intror.
    by apply or_introl.
  assert (zU : z∈ U).
    apply separation.
    apply (conj zA).    
    apply or_intror.
    by apply or_intror. 
  assert (forall a b ,a ∈ A -> b ∈ A -> <|a,b|> ∈ R -> a <> b).
    intros a b aA bA abR ab.
    subst b.
    case ((H3 a aA) abR).
  specialize (H4 x y xA yA xy) as x_y.
  specialize (H4 y z yA zA yz) as y_z.
  clear H4.
  assert (U ⊆ A).
    intros i Hi.
    apply separation in Hi.
    apply Hi. 
  assert (U <> ∅).
    intro.
    rewrite H5 in xU.
    assert (x_ : M x) by (by exists ∅).
    case ((empty x x_) xU).
  specialize (H1 U (conj H4 H5)).
  induction H1 as [m]; induction H1 as [mU].
  apply separation in mU.
  induction mU as [mA].
  induction H6 as [mx|H6].
  + subst m.    
    assert (z <> x).
      intro.
      subst z.
      specialize (H1 y (conj yU y_z)).
      induction H1.
      case (H6 yz).
    specialize (H1 z (conj zU H6)).
    apply H1. 
  + induction H6 as [my | mz].
    - subst m.
      specialize (H1 x (conj xU x_y)).
      induction H1.
      case (H6 xy).
    - subst m.
      specialize (H1 y (conj yU y_z)).
      induction H1.
      case (H6 yz).
Qed.

Theorem we_tot {R A} : 
  We R A -> Tot R A.
Proof.
  intro.
  split.
  + apply (we_tr H).
  + split.
    apply H.
    apply (we_con H).
Qed.

Theorem sub_trans {X Y Z} :
    X ⊆ Y -> Y ⊆ Z -> X ⊆ Z.
Proof.
Admitted.      

Theorem we_sub {R X Y} :
  We R X -> Y ⊆ X -> We R Y.
Proof.
  intros H YX.
  inversion H.
  inversion H0.
  split.
  + apply (conj H2).
    intros x xY.
    specialize ( YX x xY).
    apply (H3 x YX).
  + intros Z HZ.
    induction HZ as [ZY Z0] .
    specialize (sub_trans ZY YX) as ZX.
    induction (H1 Z (conj ZX Z0)) as [m].
    induction H4 as [mZ].
    by exists m.
Qed.    






  