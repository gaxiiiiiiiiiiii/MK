Require Export Properties.

Definition Un X :=
  forall x y z, M x -> M y -> M z ->
  <|x,y|> ∈ X -> <|x,z|> ∈ X -> y = z.

    
Definition Fnc X :=
  X ⊆ V² /\ Un X.

Definition Map f X Y :=
  Fnc f /\ Dom f = X /\ Ran f ⊆ Y.
Notation "f : X → Y" := (Map f X Y) (at level 10).

Definition Restriction X Y  :=
  X ∩ (Y × V).
Notation "X ∥ Y" := (Restriction X Y)(at level 10).

Theorem restriction f X g :
    g ∈ (f ∥ X) <-> exists x y, M x /\ M y /\ g = <|x,y|> /\ g ∈ f /\ x ∈ X.
Proof.
  unfold Restriction.
  rewrite cap.
  rewrite product.
  split => [H | H].
  + induction H as [gf H].
    induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [g_xy]; induction H as [xX yV].
    by exists x; exists y.
  + induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [g_xy]; induction H as [gf xX].
    apply (conj gf).
    assert (yV : y ∈ V).
    apply universe.
    apply y_.
    by exists x; exists y.
Qed.    




Definition Image X Y :=
  Ran (X ∥ Y).

Theorem image f X y (y_ : M y):
    y ∈ (Image f X) <-> exists x, M x /\ x ∈ X /\ <|x,y|> ∈ f.
Proof.
  unfold Image.
  rewrite ran.
  split => [H | H].
  + induction H as [x].
    induction H as [x_ H].
    apply restriction in H.
    induction H as [x0]; induction H as [y0].
    induction H as [x0_]; induction H as [y0_].
    induction H as [xyxy]; induction H as [xy_f xX].
    apply (OP_eq x y x0 y0 x_ y_ x0_ y0_) in xyxy; induction xyxy; subst x0 y0.
    by exists x.
  + induction H as [x]; induction H as [x_].
    induction H as [xX xy_f].
    exists x.
    apply (conj x_).
    rewrite restriction.
    by exists x; exists y.
  + apply y_.
Qed.