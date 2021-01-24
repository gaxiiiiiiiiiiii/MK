Require Export Values.

Definition Composition g f :=
  {: (Dom f) × (Ran g) | 
    fun u => exists x y z, M x /\ M y /\ M z /\
    u = <|x,z|> /\ <|x,y|> ∈ f /\ <|y,z|> ∈ g
  :}.
Notation "g ○ f" := (Composition g f) (at level 50). 

Theorem in_compos g f u:
    u ∈ (g ○ f) <-> 
    exists x y z, M x /\ M y /\ M z /\ u = <|x,z|> /\ <|x,y|> ∈ f /\ <|y,z|> ∈ g.
Proof.
  split => [H | [x [y [z [x_ [y_ [z_ [u_xz [xy_f yz_g]]]]]]]]].
  + have u_ : M u by is_set.
    by case /(in_cls _ u u_) : H.
  + subst u.
    apply in_cls => //.
    apply orderd_set => //.
    split.
    - apply in_prod.
      exists x; exists z.
      split => //; split => //; split => //; split.
      * by apply in_dom => //; exists y.
      * by apply in_ran => //; exists y.
    - by exists x; exists y; exists z.
Qed.

Theorem orderd_in_compos g f x z (x_ : M x) (z_ : M z) :
  <|x,z|> ∈ (g ○ f) <-> exists y, M y /\ <|x,y|> ∈ f /\ <|y,z|> ∈ g.
Proof.
  rewrite in_compos.
  split => [ [x0 [y [z0 [x0_ [y_ [z0_ [xzxz [xy_f fy_g]]]]]]]]
           | [y [y_ [xy_f yz_g]]]].           
  + have H : x0 = x /\ z0 = z by apply orderd_eq.
    case H => [l r]; subst x0 z0.
    by exists y.
  + by exists x; exists y; exists z.
Qed.

Theorem composition_assoc f g h :
    f ○ (g ○ h) = (f ○ g) ○ h.
Proof.
  equal => i.
  rewrite !in_compos.
  split => [ [x [y [z [x_ [y_ [z_ [i_xz [H yz_f]]]]]]]]
           | [x [y [z [x_ [y_ [z_ [i_xz [xy_f H]]]]]]]]].
  + move /(orderd_in_compos g h x y x_ y_) : H => [a [a_ [xa_h ay_g]]].
    exists x; exists a; exists z.
    split => //; split => //; split => //; split => //; split => //.
    rewrite orderd_in_compos => //.
    by exists y.
  + move /(orderd_in_compos f g y z y_ z_) : H => [a [a_ [ya_g az_f]]].
    exists x; exists a; exists z.
    split => //; split => //; split => //; split => //; split => //.
    apply orderd_in_compos => //.
    by exists y.
Qed.    

Theorem inv_compos {g f} :
  Inverse (g ○ f) = Inverse f ○ (Inverse g).
Proof.
  equal => i.
  split => [H|H]; have i_ : M i by is_set.
  + move /in_inv : H => [x [z [x_ [z_ [i_xz zx_gf]]]]].
    move /(orderd_in_compos g f z x z_ x_) : zx_gf => [y [y_ [xy_f yx_g]]].
    subst i.
    apply orderd_in_compos => //.
    exists y; split => //.
    split; rewrite orderd_in_inv => //.
  + move /(in_compos (Inverse f) (Inverse g)  i) : H => [x [y [z [x_ [y_ [z_ [i_xz H]]]]]]].
    case : H ; rewrite !orderd_in_inv => // yx_g zy_f.
    subst i; rewrite orderd_in_inv => //; rewrite orderd_in_compos => //.
    by exists y.
Qed.

Theorem un_composition {g f} :
  Un f -> Un g -> Un (g ○ f).
Proof.
  move => unf ung x y z x_ y_ z_.
  rewrite !orderd_in_compos => // [[a [a_ [xa_f ay_g]]] [b [b_ [xb_f bz_g]]]].
  suff ab : a = b.
    subst b.
    apply ung with (x := a) => //.
  apply unf with (x := x) => //.
Qed.  


    




  