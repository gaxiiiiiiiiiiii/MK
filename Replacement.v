Require Export Functions.


Axiom Replacement :
  forall f X, M X ->  Un f -> M (Image f X).  

Theorem cap_set X Y (X_ : M X)  :
    M (X ∩ Y).
Proof.
  pose (fun p => exists x, p = <|x,x|> /\ x ∈ X /\ x ∈ Y) as H0.
  pose ({| H0 |}) as f.
  assert (Unf : Un f).
  + intros x y z x_ y_ z_ xy_f yz_f.
    apply (classify H0) in xy_f.
    induction xy_f as [a]; induction H as [xy_aa]; induction H as [aX _].
    assert (a_ : M a) by (by exists X).
    apply (OP_eq x y a a x_ y_ a_ a_) in xy_aa; induction xy_aa. subst a.
    apply (classify H0) in yz_f.
    induction yz_f as [a]; induction H as [yz_aa]; induction H as [aX_ _].
    assert (a__ : M a) by (by exists X).
    apply (OP_eq x z a a x_ z_ a__ a__) in yz_aa; induction yz_aa. subst a.
    by subst x.
    by apply op_set.
    by apply op_set.
  + assert (H : X ∩ Y = Image f X).
    - apply equal => x.
      rewrite cap.      
      split => [H | H].
      * rewrite image.      
        unfold f.
        unfold H0.
        exists x.
        induction H as [xX xY] .
        assert (x_ : M x) by (by exists X).
        apply (conj x_).
        apply (conj xX).
        apply classify.
        apply (op_set x x x_ x_).
        by exists x.
        exists X.
        apply H.
      * assert (x_ : M x) by (by exists (Image f X)).
        apply image in H.      
        unfold f in H.
        unfold H0 in H.
        induction H as [x0]; induction H as[x0_]; induction H as [xX].
        apply (classify H0) in H.
        induction H as [x1]; induction H as [xx_xx]; induction H as [_ xY].
        assert (x1_ : M x1) by (by exists Y).
        apply (OP_eq x0 x x1 x1 x0_ x_ x1_ x1_) in xx_xx. induction xx_xx. subst x0 x1.
        done.
        by apply op_set.
        done.
    - rewrite H.
      by apply Replacement.
Qed.

Theorem sub_set x y (y_ : M y):
  x ⊆ y -> M x.
Proof.
  intro H.
  assert (y_xy : x = y ∩ x).
  + apply equal => i.
    rewrite cap.
    split => [iy |iyix].
    - apply (conj (H i iy)).
      apply (iy).      
    - apply iyix.
  + specialize (cap_set y x y_).
    by rewrite <- y_xy.
Qed.

Definition Separation X P :=
  {| fun x => x ∈ X /\ P x|}.
Notation "{: X | P :}" := (Separation X P) (at level 10).   

Theorem separation {X P x} :
  x ∈ ({: X | P :}) <-> x ∈ X /\ P x.
Proof.
  split => [H | H].
  + assert (x_ : M x) by (by exists ({: X | P :})) .
    by apply (classify (fun x => x ∈ X /\ P x)) in H.
  + assert (x_ : M x) by (by induction H; exists X).
    by apply (classify (fun x => x ∈ X /\ P x)).
Qed.

Theorem separation_sub X P :
  {: X | P:} ⊆ X.
Proof.
  intros x XP.
  apply separation in XP.
  apply XP.
Qed.    

Theorem separation_set X P :
  M X -> M ({: X | P :}).
Proof.
  intro X_.
  specialize (separation_sub X P) as H0.
  by apply sub_set in H0.
Qed.  



Definition Value f x :=
    {| fun i => forall y, M y -> <|x,y|> ∈ f -> i ∈ y|}.

Theorem value f x :
  Un f -> x ∈ Dom f -> <|x, Value f x|>  ∈ f.
Proof.
  intros unf H.
  assert (x_ : M x) by (by exists (Dom f)).
  apply dom in H.
  induction H as [y]; induction H as [y_ xy_f].
  assert (y_fx : y = Value f x).
  + apply equal => i.
    split => [H | H].
    - assert (i_ : M i) by (by exists y).
      apply classify.
      apply i_.
      intros y0 y0_ xy0_f.
      specialize (unf x y y0 x_ y_ y0_ xy_f xy0_f).
      by rewrite unf in H.
    - assert (i_ : M i) by (by exists (Value f x)).
      move: H; rewrite classify.
      intro H.
      by apply (H y y_ xy_f).
      apply i_.
  + by rewrite <- y_fx.
  + done.
Qed.     
