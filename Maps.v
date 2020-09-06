Require Export Infinity.


Definition Trans R A :=
  Rel R /\ forall x y z, x ∈ A -> y ∈ A -> z ∈ A -> 
  <|x,y|> ∈ R -> <|y,z|> ∈ R -> <|x,z|> ∈ R.

Definition NonRefl R A :=
  Rel R /\ forall x, x ∈ A -> ~ <|x,x|> ∈ R.

Definition Refl R A :=
Rel R /\ forall x, x ∈ A -> <|x,x|>  ∈ R.

Definition Tri R A :=
  Rel R /\ forall x y, x ∈ A -> y ∈ A ->
  <|x,y|> ∈ R \/ <|y,x|> ∈ R \/ x = y.

Definition Comm R A :=
  Rel R /\ forall x y, x ∈ A -> y ∈ A ->
  <|x,y|> ∈ R <-> <|y,x|> ∈ R.

Definition Part R A :=
  Trans R A /\ NonRefl R A.    

Definition Total R A :=
  Trans R A /\ NonRefl R A /\ Tri R A.

Definition Eq R A :=
    Trans R A /\ Comm R A /\ Refl R A.

Definition Composition g f :=
  {: (Dom f) × (Ran g) | 
    fun u => exists x y z, M x /\ M y /\ M z /\
    u = <|x,z|> /\ <|x,y|> ∈ f /\ <|y,z|> ∈ g
  :}.
Notation "g ○ f" := (Composition g f) (at level 10).    

Definition Surjection f A B :=
  f : A → B /\ Ran f = B.

Definition Injection f A B :=
  f : A → B /\ forall a a', a ∈ A -> a' ∈ A ->
  Value f a = Value f a' -> a = a'.

Definition Bijection f A B :=
  f : A → B /\ Ran f = B /\ 
  forall a a', a ∈ A -> a' ∈ A -> Value f a = Value f a' -> a = a'.


Definition Isomorphism f A B R G :=
    Bijection f A B -> forall x y, x ∈ A -> y ∈ A ->
    <|x,y|> ∈ R <-> <|Value f x, Value f y|> ∈ G.

Definition Isomorphic  A B R G :=
  exists f, Isomorphism f A B R G.

  
Definition Equivalence {R A} (H : Eq R A) x :=
  {: A | fun y => <|x,y|> ∈ R :}.


Definition to_eq {R A} (H : Eq R A) :=
  {: A × (Power A) | fun u => exists x, x ∈ A /\ u = <|x, Equivalence H x|> :}.


Definition Quotient {R A} (H : Eq R A) :=
  Image (to_eq H) A.




  
Theorem equivalence_set {R A} (H : Eq R A) x:
  M A -> M (Equivalence H x).
Proof.
  intro A_.
  apply separation_set.
  done.
Qed.    

Theorem euotient_set {R A} (H : Eq R A) :
  M A -> M (Quotient H).
Proof.
  intro A_.
  apply Replacement.
  done.
  intros x y z x_ y_ z_.
  repeat rewrite separation.
  intros H1 H2.
  induction H1 as [H1 H0].
  induction H0 as [x0]; induction H0 as [x0A].
  apply OP_eq in H0.
  induction H0; subst x y.
  induction H2 as [H2 H0].
  induction H0 as [x]; induction H0 as [xA].
  apply OP_eq in H0.
  induction H0; subst x0 z.
  done.
  done.
  done.
  by exists A.
  apply equivalence_set.
  done.
  done.
  done.
  by exists A.
  apply equivalence_set.
  done.
Qed.  


    


Theorem composition g f u:
    u ∈ (g ○ f) <-> 
    exists x y z, M x /\ M y /\ M z /\ u = <|x,z|> /\ <|x,y|> ∈ f /\ <|y,z|> ∈ g.
Proof.
  split => [H | H].
  + assert (u_ : M u) by (by exists (g ○ f)).
    move : H.
    rewrite separation.
    intro H.
    apply H.
  + induction H as [x]; induction H as [y]; induction H as [z].
    induction H as [x_]; induction H as [y_]; induction H as [z_].
    induction H as [u_xy]; induction H as [xy_f yz_g].
    assert (u_ : M u).
    - rewrite u_xy.
      apply (op_set x z x_ z_).
    - apply separation.
      split.
      apply product.
      exists x; exists z.
      refine (conj x_ (conj z_ (conj u_xy _))).
      split.
      * apply dom.
        done.
        by exists y.
      * apply ran.
        done.
        by exists y.
      * by exists x; exists y; exists z.        
Qed.        

      


Theorem composition_assoc f g h :
    f ○ (g ○ h) = (f ○ g) ○ h.
Proof.
  apply equal => i.
  repeat rewrite composition.
  split => [H | H].
  + induction H as [x]; induction H as [y]; induction H as [z].
    induction H as [x_]; induction H as [y_]; induction H as [z_].
    induction H as [u_xz]; induction H as [xy_gh yz_f].
    apply separation in xy_gh.
    induction xy_gh as [H0 H].
    induction H as [x0]; induction H as [y0]; induction H as [z0].
    induction H as [x0_]; induction H as [y0_]; induction H as [z0_].
    induction H as [xyxy]; induction H as [xy_h yz_g].
    apply (OP_eq x y x0 z0 x_ y_ x0_ z0_) in xyxy.
    induction xyxy; subst x0 z0.
    exists x; exists y0; exists z.
    refine (conj x_ (conj y0_ (conj z_ (conj u_xz (conj xy_h _))))).
    apply composition.
    by exists y0; exists y; exists z.
  + induction H as [a]; induction H as [b]; induction H as [d].
    induction H as [a_]; induction H as [b_]; induction H as [d_]   .
    induction H as [i_ab]; induction H as [ab_h bd_fg].
    apply composition in bd_fg.
    induction bd_fg as [b0]; induction H as [c]; induction H as [d0].
    induction H as [b0_]; induction H as [c_]; induction H as [d0_].
    induction H as [bdbd]; induction H as [bc_g cd_f].
    apply (OP_eq b d b0 d0 b_ d_ b0_ d0_) in bdbd.
    induction bdbd; subst b0 d0.
    exists a; exists c; exists d.
    apply (conj a_).
    apply (conj c_).
    apply (conj d_).
    apply (conj i_ab).
    split.
    - apply composition.
      by exists a; exists b; exists c.
    - done.
Qed.    

Theorem inverse_dom f :
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

Theorem inverse_ran f :
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

Theorem in_inverse f a b (a_ : M a) (b_ : M b):
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



Theorem inverse_bijection f A B :
  (f : A → B /\ (Inverse f) : B → A) <-> Bijection f A B.
Proof.
  split => [H | H].
  + induction H as [fAB gBA].
    unfold Bijection.
    apply (conj fAB).
    unfold Map in gBA.
    unfold Fnc in gBA.
    induction gBA as [funcf H].
    induction H as [dom_B ranf_A].
    split.
    - rewrite <- dom_B.
      symmetry.
      apply inverse_dom.
    - intros a b aA bA H.
      assert (a_ : M a) by (by exists A).
      assert (b_ : M b) by (by exists A).
      induction fAB.
      induction H1.
      induction H0.
      induction funcf as [_ unf].
      rewrite <- H1 in aA.
      specialize (value f a H3 aA) as v.
      induction v.
      apply (unf (Value f a) a b).
      done.            
      done.
      done.
      * apply inverse.
        by exists (Value f a); exists a.
      * rewrite H in H4.
        rewrite H.
        apply inverse.
        rewrite <- H1 in bA.
        specialize (value f b H3 bA) as H6.
        induction H6.
        by exists (Value f b); exists b.
  + induction H.
    apply (conj H).
    induction H.
    induction H.
    induction H1.
    induction H0.
    split.
    - split.
      * intros p h.
        apply inverse in h.        
        induction h as [y h]; induction h as [x h].        
        induction h as [y_ h]; induction h as [x_ h].
        induction h as [p_yx xy_f].
        apply product.
        exists y; exists x.
        by repeat rewrite universe.
      * intros a b c a_ b_ c_ ab_f ac_f.
        apply inverse in ab_f.
        induction ab_f as [x h]; induction h as [y h].
        induction h as [x_ h]; induction h as [y_ h].
        induction h as [abxy ba_f].
        apply (OP_eq a b x y a_ b_ x_ y_) in abxy.
        induction abxy; subst x y.
        clear x_ y_.
        apply inverse in ac_f.
        induction ac_f as [x h]; induction h as [y h].
        induction h as [x_ h]; induction h as [y_ h].
        induction h as [abxy ca_f].
        apply (OP_eq a c x y a_ c_ x_ y_) in abxy.
        induction abxy; subst x y.
        clear x_ y_.
        apply H4.
        rewrite <- H1.
        apply dom.
        done.
        by exists a.
        rewrite <- H1.
        apply dom.
        done.
        by exists a.        
        assert (a = Value f b).
        apply (eq_value f b a b_ a_ H2).
        apply dom.
        done.
        by exists a.
        done.
        assert (a = Value f c).
        apply (eq_value f c a c_ a_ H2).
        apply dom.
        done.
        by exists a.
        done.
        rewrite <- H5.
        by rewrite <- H6.
    - split.
      * rewrite <- H0.
        apply inverse_dom.
      * rewrite inverse_ran.
        rewrite <- H1.
        intros i iH.
        done.
Qed.  


Definition Identity X :=
  {: X × X | fun u => exists x, x ∈ X /\ u = <|x,x|>:}.

Theorem identity X u :
  u ∈ Identity X <->  exists x, x ∈ X /\ u = <|x,x|>.
Proof.
  split => [H | H].
  (* + assert (u_ : M u) by (by exists (Identity X)). *)
  + apply separation in H.
    by induction H.
  + induction H as [x]; induction H as [Xx u_xx].
    assert (x_ : M x) by (by exists X).
    rewrite separation.
    split.
    - rewrite product.
      by exists x; exists x.
    - by exists x.
Qed.

Theorem identity_set X :
  M X -> M (Identity X).
Proof.
  intro X_.
  apply separation_set.
  by apply product_set.
Qed.

Theorem inverse_composition_left f A B :
  f : A → B -> (Inverse f) : B → A -> (Inverse f) ○ f = Identity A.
Proof.
  intros fAB fBA.
  rewrite equal => p.
  rewrite composition.
  rewrite identity.
  split => [H | H].
  + induction H as [x]; induction H as [y]; induction H as [z].
    induction H as [x_]; induction H as [y_]; induction H as [z_].
    induction H as [p_xz]; induction H as [xy_f yz_f].
    apply inverse in yz_f.
    induction yz_f as [x0]; induction H as [y0].
    induction H as [x0_]; induction H as [y0_].
    induction H as [yzyz zy_f].
    apply (OP_eq y z x0 y0 y_ z_ x0_ y0_) in yzyz; clear x0_ y0_.
    induction yzyz; subst x0 y0.
    assert (x = z).
    - induction fBA.
      induction H.
      apply (H1 y x z y_ x_ z_).
      * rewrite inverse.
        by exists y; exists x.
      * rewrite inverse.
        by exists y; exists z.
    - subst z.
      exists x.
      split.
      * induction fAB.
        induction H0.
        rewrite <- H0.
        apply dom.
        done.
        by exists y.
      * done.
  + induction H as [x]; induction H as [xA p_xx].
    induction fAB.
    induction H.
    induction H0.
    assert (x_ : M x) by (by exists A).
    assert (<|x,Value f x|> ∈ f).
    - apply (value f x H1).
      by rewrite <- H0 in xA.
    - assert (<|Value f x, x|> ∈ Inverse f).
      assert (M (Value f x)).
      apply value_set.
      apply H1.
      by rewrite <- H0 in xA.
      * apply inverse.
        by exists (Value f x); exists x.
      * exists x; exists (Value f x); exists x.
        split.
        done.
        split.
        apply value_set.
        apply H1.
        by rewrite <- H0 in xA.
        done.
Qed.

Theorem inverse_composition_right f A B :
  f : A → B -> (Inverse f) : B → A -> f ○ (Inverse f) = Identity B.
Admitted.

Theorem double_inverse f:
    Rel f -> Inverse (Inverse f) = f.
Proof.
  intro relf.
  apply equal => i.
  rewrite inverse.
  split => [H | H].
  + induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [i_xy yx_f].
    apply (in_inverse f y x y_ x_) in yx_f.
    by rewrite <- i_xy in yx_f.
  + specialize (relf i H).
    apply product in relf.
    induction relf as [x]; induction H0 as [y].
    induction H0 as [x_]; induction H0 as [y_].
    induction H0 as [i_xy _].
    exists x; exists y.
    refine (conj x_ (conj y_ (conj i_xy _))).
    apply inverse.
    rewrite i_xy in H.
    by exists y; exists x.
Qed.




   







    








      
      
     
    








