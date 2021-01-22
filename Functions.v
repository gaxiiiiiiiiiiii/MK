Require Export Properties.

Definition Un X :=
  forall x y z, M x -> M y -> M z ->
  <|x,y|> ∈ X -> <|x,z|> ∈ X -> y = z.


    
Definition Fnc X :=
  Rel X /\ Un X.

Definition Map f X Y :=
  Fnc f /\ Dom f = X /\ Ran f ⊂ Y.
Notation "f : X → Y" := (Map f X Y) (at level 10).

Definition Restriction f X  :=
  f ∩ (X × V).
Notation "f | ( X )" := (Restriction f X)(at level 10).

Theorem in_restrict f X g :
    g ∈ (f | (X)) <-> exists x y, M x /\ M y /\ g = <|x,y|> /\ g ∈ f /\ x ∈ X.
Proof.
  unfold Restriction.
  rewrite in_cap.
  rewrite in_prod.
  split => [ [gf [x [y [ x_ [y_  [g_xy [ xX _]]]]]]] | [x [y [x_ [y_ [g_xy [gf xX]]]]]]]; [|split] => //; exists x; exists y => //.
  by rewrite in_universe.
Qed.    


Definition Image f X :=
  Ran (f | (X)).

Theorem in_image f X y (y_ : M y):
    y ∈ (Image f X) <-> exists x, M x /\ x ∈ X /\ <|x,y|> ∈ f.
Proof.
  unfold Image.
  rewrite in_ran => //.
  split => [[x [x_ H]]| [x [x_ [xX xy_f]]]].
  + move /in_restrict : H => [x0 [y0 [x0_ [y0_ [xyxy [xy_f xX]]]]]].
    move /(orderd_eq x y x0 y0 x_ y_ x0_ y0_) : xyxy => [xx0 yy0]; subst x0 y0.
    by exists x.
  + exists x; split => //; rewrite in_restrict.
    by exists x ; exists y.
Qed.    