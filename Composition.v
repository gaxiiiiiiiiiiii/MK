Require Export Values.

Definition Composition g f :=
  {: (Dom f) × (Ran g) | 
    fun u => exists x y z, M x /\ M y /\ M z /\
    u = <|x,z|> /\ <|x,y|> ∈ f /\ <|y,z|> ∈ g
  :}.
Notation "g ○ f" := (Composition g f) (at level 10). 

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

Theorem in_composition g f x z (x_ : M x) (z_ : M z) :
  <|x,z|> ∈ (g ○ f) <-> exists y, M y /\ <|x,y|> ∈ f /\ <|y,z|> ∈ g.
Proof.
  split => [H | H].
  + apply composition in H.
    induction H as [x0]; induction H as [y]; induction H as [z0].
    induction H as [x0_]; induction H as [y_]; induction H as [z0_].
    induction H as [xz]; induction H.
    apply (OP_eq x z x0 z0 x_ z_ x0_ z0_) in xz.
    induction xz; subst x0 z0.
    by exists y.
  + induction H as [y]; induction H as [y_].
    induction H.
    apply composition.
    by exists x; exists y; exists z.
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

Theorem inverse_composition {g f} :
  Inverse (g ○ f) = Inverse f ○ (Inverse g).
Proof.
  apply equal => i.
  rewrite composition.
  rewrite inverse.
  split => [H | H].
  + induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [i_xy xy_gf].
    apply in_composition in xy_gf.
    induction xy_gf as [u]; induction H as [u_].
    induction H.
    exists x; exists u; exists y.
    by repeat rewrite in_inverse.
    done.
    done.
  + induction H as [x]; induction H as [y]; induction H as [z].
    induction H as [x_]; induction H as [y_]; induction H as [z_].
    induction H as [i_xz]; induction H as [yx_g zy_f].
    move : yx_g zy_f.
    repeat rewrite in_inverse.
    intros yx_g zy_f.
    exists x; exists z.
    apply (conj x_).
    apply (conj z_).
    apply (conj i_xz).
    apply in_composition.
    done.
    done.
    by exists y.
    done.
    done.
    done.
    done.
Qed.

Theorem un_composition {g f} :
  Un f -> Un g -> Un (g ○ f).
Proof.
  intros un_f un_g.
  intros x y z x_ y_ z_.
  repeat rewrite in_composition.
  intros.
  induction H as [y0]; induction H as [y0_].
  induction H as[xy0_f y0y_g].
  induction H0 as [z0]; induction H as [z0_].
  induction H as [xz0_f z0z_g].
  specialize (un_f x y0 z0 x_ y0_ z0_ xy0_f xz0_f) as H.
  subst z0.
  by specialize (un_g y0 y z y0_ y_ z_ y0y_g z0z_g).
  done.
  done.
  done.
  done.
Qed.  

Theorem dom_composition {g f } :
  Un₁ f -> Un₁ g -> Dom (g ○ f) = Dom f.
Proof.
  intros un1_f un1_g.
  apply equal => x.
  split => [H | H].
  + assert (x_ : M x) by (by exists (Dom (g ○ f))).
    apply dom in H.
    induction H as [z]; induction H as [z_].
    apply in_composition in H.
    induction H as [y]; induction H as [y_].
    induction H.
    apply dom.
    done.
    by exists y.
    done.
    done.
    done.
  + assert (x_ : M x) by (by exists (Dom f)).
    apply dom in H.
    induction H as [y]; induction H as [y_].
    apply dom.
    done.
    induction un1_f as [un_f un_f_].
    induction un1_g as [un_g un_g_].
    specialize (value g y).
    exists (Value g y).
    split.
    - apply value_set.
      done.
      apply dom.
      done.
      exists (Value g y).




  