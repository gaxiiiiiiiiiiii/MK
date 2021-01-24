Require Export Replacement.


Theorem dom_inverse {f} :
  Dom (Inverse f) = Ran f.
  Proof.
    equal => x.
    split => [H | H]; have x_ : M x by is_set.
    + move /(in_dom _ x x_) : H => [y [y_ xy_f']].
      move /in_inv : xy_f' => [x0 [y0 [x0_ [y0_ [xyxy yx_f]]]]].
      move /(orderd_eq x y x0 y0 x_ y_ x0_ y0_) : xyxy => [xx yy]; subst x0 y0 => {x0_ y0_}.
      rewrite in_ran => //.
      by exists y.
    + move /(in_ran _ x x_) : H => [y [y_ yx_f]].
      rewrite in_dom => //.
      exists y; split => //.
      rewrite in_inv => //.
      by exists x; exists y.
  Qed.

Theorem ran_inverse {f} :
  Ran (Inverse f) = Dom f.
  Proof.
    equal => x.
    split => [H | H]; have x_ : M x by is_set.
    + move /(in_ran _ x x_) : H => [y [y_ H]].
      move /in_inv : H => [y0 [x0 [y0_ [x0_ [xyxy xy_f]]]]].
      move /(orderd_eq y x y0 x0 y_ x_ y0_ x0_) : xyxy => [yy xx]; subst x0 y0 => {x0_ y0_}.
      rewrite in_dom => //.
      by exists y.
    + move /(in_dom _ x x_) : H => [y [y_ xy_f]].
      rewrite in_ran => //.
      exists y; split => //.
      rewrite in_inv.
      by exists y; exists x.
Qed.




Theorem orderd_in_inv {f a b} {a_ : M a} {b_ : M b}:
  <|a,b|> ∈ Inverse f <-> <|b,a|> ∈ f.
Proof.
rewrite in_inv.
split => [[x [y [x_ [y_ [abxy yx_f]]]]] | H].
+ by move /(orderd_eq a b x y a_ b_ x_ y_) : abxy => [ax yb]; subst a b.
+ by exists a; exists b.
Qed.




Theorem value_inv_value f x :
  Un₁ f -> x ∈ Dom f -> x = Value (Inverse f) (Value f x).
Proof.
  move =>  [unf unf'] domf.
  have x_ : M x by is_set.  
  apply (in_dom _ x x_) in domf as H.
  move : H => [y [y_ xy_f]].
  apply (in_value) in xy_f  as y_fx => //.
  rewrite -y_fx.
  have yx_f' : <|y,x|> ∈ Inverse f.
    rewrite orderd_in_inv => //.
  apply in_value => //.
  rewrite dom_inverse.
  rewrite in_ran => //.
  by exists x.
Qed.  



Theorem inv_inv {f} :
  Rel f -> Inverse (Inverse f) = f.
Proof.
  move =>  rel_f.
  equal => i.
  split => [H|H]; have i_ : M i by is_set.
  + move /in_inv : H => [x [y [x_ [y_ [i_xy yx_f']]]]]; subst i.
    rewrite -orderd_in_inv => //.
  + move : (rel_f i H).
    move /in_prod => [x [y [x_ [y_ [i_xy _]]]]]; subst i.
    rewrite orderd_in_inv => //.
    rewrite orderd_in_inv => //.
Qed.    

  
