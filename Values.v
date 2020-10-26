Require Export Infinity.


Theorem dom_inverse {f} :
  Dom (Inverse f) = Ran f.
  Proof.
    apply equal => x.
    split => [H | H].
    + assert (x_ : M x) by (by exists (Dom (Inverse f))).
      apply dom in H.
      apply ran.
      done.
      induction H as [y]; induction H as [y_].
      apply inverse in H.
      induction H as [x0]; induction H as [y0].
      induction H as [x0_]; induction H as [y0_].
      induction H as [xyxy xy_f].
      apply (OP_eq x y x0 y0 x_ y_ x0_ y0_) in xyxy.
      induction xyxy; subst x0 y0.
      by exists y.
      done.
    + assert (x_ : M x) by (by exists (Ran f)).
      apply ran in H.
      induction H as [y]; induction H as [y_].
      rewrite dom.
      exists y.
      apply (conj y_).
      rewrite inverse.
      by exists x; exists y.
      done.
      done.
  Qed.

Theorem ran_inverse {f} :
  Ran (Inverse f) = Dom f.
  Proof.
    apply equal => x.
    split => [H | H].
    + assert (x_ : M x) by (by exists (Ran (Inverse f))).
      apply ran in H.
      induction H as [y]; induction H as [y_].
      apply inverse in H.
      induction H as [y0]; induction H as [x0].
      induction H as [y0_]; induction H as [x0_].
      induction H as [yxyx xy_f].
      apply (OP_eq y x y0 x0 y_ x_ y0_ x0_) in yxyx.
      induction yxyx; subst y0 x0.
      apply dom.
      done.
      by exists y.
      done.
    + assert (x_ : M x) by (by exists (Dom f)).
      apply dom in H.
      induction H as [y]; induction H as [y_ xy_f].
      apply ran.
      done.
      exists y.
      apply (conj y_).
      apply inverse.
      by exists y; exists x.
      done.
  Qed.

Theorem in_inverse {f a b} {a_ : M a} {b_ : M b}:
  <|a,b|> ∈ Inverse f <-> <|b,a|> ∈ f.
Proof.
rewrite inverse.
split => [H | H]      .
+ induction H as [x]; induction H as [y].
  induction H as [x_]; induction H as [y_].
  induction H as [abxy ba_f].
  apply (OP_eq a b x y a_ b_ x_ y_) in abxy.
  by induction abxy; subst x y.
+ by exists a; exists b.
Qed.

Theorem eq_value f a b (a_ : M a) (b_ : M b) :
  Un f -> a ∈ Dom f -> <|a,b|> ∈ f <-> b = Value f a.
Proof.
  intros unf domf.
  specialize (value f a unf domf) as H.
  induction H.
  split => [H1 | H1].
  + apply (unf a b (Value f a) a_ b_ H0 H1 H).
  + by rewrite H1.
Qed.   



Theorem value_value f x :
  Un₁ f -> x ∈ Dom f -> x = Value (Inverse f) (Value f x).
Proof.
  intros unf domf.
  induction unf.
  specialize (value f x H domf) as H1.
  induction H1.
  assert (x_ : M x) by (by exists (Dom f)).
  assert (Value f x ∈ Dom (Inverse f)).
    rewrite dom_inverse.
    rewrite ran.
    by exists x.
    done.
  rewrite <- (eq_value (Inverse f) (Value f x) x H2 x_ H0 H3).
  by rewrite in_inverse.
Qed.  


Theorem inverse_inverse {f} :
  Rel f -> Inverse (Inverse f) = f.
Proof.
  intro rel_f.
  apply equal => i.
  split => [H | H].
  + apply inverse in H.
    induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [i_xy xy_f].
    apply (@in_inverse f y x y_ x_) in xy_f.
    by subst i.
  + specialize (rel_f i H).
    apply product in rel_f.
    induction rel_f as [x]; induction H0 as [y].
    induction H0 as [x_]; induction H0 as [y_].
    induction H0 as [i_xy _].
    subst i.
    apply (@in_inverse (Inverse f) x y x_ y_).
    by apply (@in_inverse f y x y_ x_).
Qed.    

  
