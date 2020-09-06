Require Export Maps.

Definition Max R X x :=
  ~ exists y, y ∈ X /\ <|x,y|> ∈ R.

Definition Min R X x :=
  ~ exists y, y ∈ X /\ <|y,x|> ∈ R.

Definition WellFounded R A :=
  forall X, X ⊆ A -> exists x, Min R X x.

Definition WellOrderd R A :=
    Total R A /\ WellFounded R A.

    
Theorem sub_wellorderd R A :
  WellOrderd R A -> forall X, X ⊆ A -> WellOrderd R X.
Proof.
  intros H X XA.
  unfold WellOrderd.
  unfold Total.
  unfold Trans.
  unfold NonRefl.
  unfold Tri.
  unfold WellFounded.
  induction H.
  induction H.
  induction H.
  induction H1.
  induction H1 as [_ H1].
  induction H3 as [_ H3].  
  unfold WellFounded in H0.
  split.
  split.
  + apply (conj H).
    intros x y z xX yX zX xyR yzR.
    apply (H2 x y z (XA x xX) (XA y yX) (XA z zX) xyR yzR).
  + split.
    - apply (conj H).
      intros x xX.
      apply (H1 x (XA x xX)).
    - apply (conj H).
      intros x y xX yX.
      apply (H3 x y (XA x xX) (XA y yX)).
  + intros Y YX.
    apply H0.
    intros i iY.
    apply XA.
    apply YX.
    done.
Qed.

Definition TransSet X :=
    M X /\ forall x, x ∈ X -> x ⊆ X.

Definition InRel :=
    {|fun p => exists x y, M x /\ M y /\ p = <|x,y|> /\ x ∈ y|}.

Theorem inrel x y (x_ : M x) (y_ : M y):
   <|x,y|> ∈ InRel <-> x ∈ y.
Proof.
  rewrite classify.
  split => [H | H].
  + induction H as [x0]; induction H as [y0].
    induction H as [x0_]; induction H as [y0_].
    induction H.
    apply (OP_eq x y x0 y0 x_ y_ x0_ y0_) in H.
    by induction H; subst x0 y0.
  + by exists x; exists y.
  + by apply op_set.
Qed.

Definition Ord X :=
    TransSet X /\ WellOrderd InRel X.

Definition ON :=
  {|Ord|}.

Theorem on X :
    X ∈ ON <-> Ord X.
Proof.
  split => [H | H].
  + assert (X_ : M X) by (by exists ON).
    move : H.
    rewrite classify.
    auto.
    done.
  + inversion H.
    induction H0 as [X_ _].   
    by apply classify.
Qed.    

Theorem on_trnas X:
    X ∈ ON -> X ⊆ ON.
Proof.
  intros XON x xX.
  assert (x_ : M x) by (by exists X).
  apply on in XON.
  induction XON.
  induction H as [X_ H].
  inversion H0.
  induction H1.
  induction H1.
  apply on.
  split.
  + apply (conj x_) .
    intros y yx z zy.
    specialize (H x xX y yx) as yX.
    specialize (H y yX z zy) as zX.
    rewrite <- inrel.
    apply inrel in zy.
    apply inrel in yx.
    apply (H4 z y x zX yX xX zy yx).    
    by exists X.
    by exists X.
    by exists X.
    by exists X.
    by exists X.
    by exists X. 
  + apply (sub_wellorderd InRel X).
    done.
    apply (H x xX).
Qed.    






