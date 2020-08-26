Require Export Existance.

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



Definition Un₁ X := Un X /\ Un (X⁰).

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


Parameter Value : Class -> Class -> Class.

Axiom value: 
  forall f x, Un f -> M (Value f x) /\ <|x, Value f x|>  ∈ f.
    (* IF Un f then M (Value f x) /\ <|x, Value f x|>  ∈ f else Value f x = ∅. *)




Goal forall f X , Fnc f -> forall y, M y -> 
      y ∈ (Image f X) <-> (exists x, M x /\ x ∈ (X ∩ (Dom f)) /\ y = Value f x).
Proof.
  intros f X funcf y y_.
  induction funcf as [f_V2 Unf].
  split => [H | H].
  + apply ran in H.
    induction H as [x]; induction H as [x_].
    induction (value f x Unf) as [fx_ xfx_f].
    apply cap in H.
    induction H as [xy_f H].
    apply product in H.
    induction H as [x0]; induction H as [y0]; induction H as [x0_]; induction H as [y0_].
    induction H as [xyxy]; induction H as [xX yV].
    apply (OP_eq x y x0 y0 x_ y_ x0_ y0_) in xyxy.
    induction xyxy; subst x0 y0.
    clear x0_ y0_.
    exists x.
    apply (conj x_).
    split.
    - apply cap.
      apply (conj xX).
      apply dom.
      apply x_.
      by exists y.
    - apply (Unf x y (Value f x) x_ y_ fx_ xy_f xfx_f).
    - apply y_.
  + apply (image f X y y_).
    induction H as [x]; induction H as [x_].
    induction H as [H y_fx].
    apply cap in H.
    induction H as [xX _].
    specialize (value f x Unf) as H.
    induction H as [_ xfx_f].
    rewrite <- y_fx in xfx_f.
    by exists x.
Qed.




Axiom R :
  forall f X, M X ->  Un f -> M (Image f X).      



Goal forall x Y, M x -> exists z, M z /\
     (forall u, M u -> u ∈ z <-> u ∈ x /\ u ∈ Y).
Proof.
  intros x Y x_.
  specialize R as H.
  specialize (H ({|fun u => exists i, u = <|i,i|> /\ i ∈ x /\ i ∈ Y|})).
  assert (Unf : Un ({|fun u : Class => exists i : Class, u = <| i, i |> /\ i ∈ x /\ i ∈ Y|}) ).
  + intros a b c a_ b_ c_ ab_f ac_f.
    apply (comprehension (fun u => exists i, u = <| i, i |> /\ i ∈ x /\ i ∈ Y)) in ab_f.
    apply (comprehension (fun u => exists i, u = <| i, i |> /\ i ∈ x /\ i ∈ Y)) in ac_f.
    induction ab_f as [i H0]; induction H0 as [abii H0]; induction H0 as [ix iY].
    assert (i_ : M i) by (by exists Y).
    apply (OP_eq a b i i a_ b_ i_ i_) in abii.
    induction abii; subst i.
    induction ac_f as [i H0]; induction H0 as [abii H0]; induction H0 as [ix0 iY0].
    assert (i__ : M i) by (by exists Y).
    apply (OP_eq a c i i a_ c_ i__ i__) in abii.
    by induction abii; subst i a b.
    apply nop_set.
    apply nop_set.
  + specialize (H x x_ Unf).
    induction H as [U H].
    exists (Image
    ({|fun u : Class => exists i : Class, u = <| i, i |> /\ i ∈ x /\ i ∈ Y|})
    x).
    split.
    - by exists U.
    - intros u u_ .
      rewrite image.
      split => [H0 | H0].
      * induction H0 as [i]; induction H0 as [i_].
        induction H0 as [ix H0].
        apply (comprehension (fun u => exists i, u = <| i, i |> /\ i ∈ x /\ i ∈ Y)) in H0.
        induction H0 as [i0]; induction H0 as [ii].
        assert (i0_ : M i0) by (by induction H0; exists x).
        apply (OP_eq i u i0 i0 i_ u_ i0_ i0_) in ii.
        by induction ii; subst i0 u.
        apply nop_set.
      * exists u.
        apply (conj u_).
        apply (conj (proj1 H0)) .
        apply (comprehension (fun u => exists i, u = <| i, i |> /\ i ∈ x /\ i ∈ Y)).
        apply nop_set.
        by exists u.
      * apply u_. 
Qed.

Definition Separation X P :=
  {| fun x => x ∈ X /\ P x|}.
Notation "{! X | P !}"  := (Separation X P)(at level 10).

Theorem separation {X P x} :
  x ∈ ({! X | P !}) <-> x ∈ X /\ P x.
Proof.
  split => [H | H].
  + assert (x_ : M x) by (by exists ({! X | P !})) .
    by apply (comprehension (fun x => x ∈ X /\ P x)) in H.
  + assert (x_ : M x) by (by induction H; exists X).
    by apply (comprehension (fun x => x ∈ X /\ P x)).
Qed.


Theorem speparation_subset X P :
  {! X | P !} ⊆ X.
Proof.
  intros x xXP.
  apply separation in xXP.
  apply xXP.
Qed.

Theorem separation_set X P (X_ : M X):
  M ({! X | P!}).
Proof.
  apply (subset_set X ({! X | P !}) X_).
  apply speparation_subset.
Qed.  


Print Rel.