Require Export Functions.


Axiom Replacement :
  forall f X, M X ->  Un f -> M (Image f X).  
        

Theorem cap_set X Y (X_ : M X)  :
    M (X ∩ Y).
Proof.
  pose (fun p => exists x, p = <|x,x|> /\ x ∈ X /\ x ∈ Y) as H0.
  pose ({| H0 |}) as f.
  have Un_f : Un f.
    rewrite /Un => x y z x_ y_ z_ xy_f xz_f.
    have xy_ : M <|x,y|> by apply orderd_set.
    have xz_ : M <|x,z|> by apply orderd_set.
    move /(in_cls _ _ xy_) : xy_f => [x0 [xyxx [xX xY]]].
    move /(in_cls _ _ xz_) : xz_f => [z0 [xzxx [_ zY]]].
    have x0_ : M x0 by is_set.
    have z0_ : M z0 by is_set.
    move /(orderd_eq x y x0 x0 x_ y_ x0_ x0_) : xyxx => [l r]; subst x y.
    move /(orderd_eq x0 z z0 z0 x0_ z_ z0_ z0_) : xzxx => [l r]; subst x0 z.
    done.
  have XY_imfX : X ∩ Y = Image f X.
    equal => i.
    rewrite in_cap.
    split => [[iX iY]|H]; have i_ : M i by is_set.
    + rewrite in_image => //.
      exists i; split => //; split => //.
      rewrite in_cls.
      by exists i.
      by apply orderd_set.
    + move /(in_image f X i i_) : H => [x [x_ [xX xi_f]]].
      have xi_ : M <|x,i|> by (apply orderd_set).
      move /(in_cls _ _ xi_) : xi_f => [j [xijj [jX jY]]].
      have j_ : M j by is_set.
      move /(orderd_eq x i j j x_ i_ j_ j_) : xijj => [xj ij]; subst i.
      done.
  + by rewrite XY_imfX; apply Replacement.
Qed.

Theorem sub_set x y (y_ : M y):
  x ⊂ y -> M x.
Proof.
  move => xy.
  suff x_xy : x = y ∩ x.
    rewrite x_xy.
    by apply cap_set.
  equal => i.
  rewrite in_cap.
  split => [ix | [iy ix]] => //.
  split => //.
  apply xy => //.
Qed.

Definition Separation X P :=
  {| fun x => x ∈ X /\ P x|}.
Notation "{: X | P :}" := (Separation X P) (at level 10).   

Theorem in_sep {X P x} :
  x ∈ ({: X | P :}) <-> x ∈ X /\ P x.
Proof.
  split => [H | [xX Px]]; have x_ : M x by is_set.
  + move /in_cls : H; auto.
  + by apply in_cls. 
Qed.

Theorem sep_sub X P :
  {: X | P:} ⊂ X.
Proof.
  move => x.
  rewrite in_sep.
  by case.
Qed.    

Theorem sep_set X P :
  M X -> M ({: X | P :}).
Proof.
  move => X_.
  apply sub_set with (y := X) => //.
  apply sep_sub.
Qed.  




  
  



Theorem dom_set f (f_ : M f):
    M (Dom f).
Proof.
  apply sub_set with (y := ⊔ ⊔ f).
  + by apply cups_set; apply cups_set.
  + move => i H.
    have i_ : M i by is_set.
    move /(in_dom _ _ i_) : H => [y [y_ iy_f]].
    rewrite in_cups.
    exists (Single i ); split.
    apply single_refl => //.
    apply in_cups.
    exists <|i,y|>; split => //.
    apply in_orderd => //.
    apply single_set => //.
    left => //.
Qed.

Theorem ran_set f (f_ : M f) :
    M (Ran f).
Proof.
  apply sub_set with (y := ⊔ ⊔ f).
  + by apply cups_set; apply cups_set.
  + move => i H.
    have i_ : M i by is_set.
    move /(in_ran f i i_) : H => [x [x_ xi_f]].
    apply in_cups.
    exists (Pair x i); split.
    apply in_pair => //; right => //.
    apply in_cups.
    exists <|x,i|>; split => //.
    apply in_orderd => //.
    apply pair_set => //.
    right => //.
Qed.    




Theorem cup_set x y (x_ : M x) (y_ : M y):
  M (x ∪ y).
Proof.
  apply sub_set with (y := ⊔ (Pair x y)).
  + by apply cups_set; apply pair_set.
  + move => i H.
    move /in_cup : H => H.
    apply in_cups.
    case H => [ix | iy].
    - exists x; split => //.
      apply in_pair => //; left => //.
    - exists y; split => //.
      apply in_pair => //; right => //.
Qed.      

  

Theorem product_set x y (x_ : M x) (y_ : M y) :
    M (x × y).
Proof.
  apply sub_set with (y := Power (Power (x ∪ y))).
  + by apply pow_set; apply pow_set; apply cup_set.
  + move => i H.
    have i_ : M i by is_set.
    move /(in_prod x y i) : H => [x0 [y0 [x0_ [y0_ [i_xy [xx yy]]]]]].
    apply in_pow => //.
    move => j ji.
    apply in_pow => //; is_set.
    move => k kj.
    apply in_cup.
    subst i.
    have j_ : M j by  is_set.
    have k_ : M k by is_set.    
    move /(in_orderd x0 y0 j x0_ y0_ j_) : ji => [jxx | jxy]; subst j.
    - by move /(in_single x0 k k_) : kj ->; left.
    - by case /(in_pair x0 y0 k k_) : kj => [kx|ky]; [left|right]; subst k.
Qed.      

      


Theorem not_empty x :
  x <> ∅ <-> exists y, y ∈ x.
Proof.
  split => [Hx|[y yx] Hx].
  + apply NNPP => F.
    move /not_ex_all_not : F => H.
    apply Hx.
    equal => i.
    split => [ix | F].
    - case ((H i) ix).
    - suff i0 : ~ i ∈ ∅.
        case (i0 F).
      apply notin_empty; is_set.
  + suff F : (~ y ∈ ∅).
      by apply F; subst x.
    apply notin_empty; is_set.
Qed.    

Theorem caps_set X :
  X <> ∅ -> M (⊓ X).
Proof.
  move /not_empty => [x xX].
  apply sub_set with (y := x).
  + is_set.
  + move => i H.
    have i_ : M i by is_set.
    by move /(in_caps X i i_) : H ; apply.
Qed.    


Definition Inverse f :=
  {: (Ran f) × (Dom f) |
   fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ <|y,x|> ∈ f 
  :}.

Theorem in_inv f u :
  u ∈ Inverse f <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ <|y,x|> ∈ f.
Proof.
  split => [H | [x [y [x_ [y_ [u_xy yx_f]]]]]].
  + have u_ : M u by is_set.
    move /(in_cls _ u u_) : H => [H [x [y [x_ [y_ [u_xy yx_f]]]]]].
    by exists x; exists y.
  + rewrite in_cls => //.      
    * split.
      - rewrite in_prod.
        exists x; exists y.
        split => //; split => //; split => //; split.
        apply in_ran => //; exists y => //.
        apply in_dom => //; exists x => //.
      - by exists x; exists y.
    * subst u; apply orderd_set => //.
Qed.      
     


Definition Un₁ X := Un X /\ Un (Inverse X).

Definition Value f x :=
  ⊓ {| fun y => <|x,y|> ∈ f|}.
Notation "f [ x ]" := (Value f x) (at level 5).

Theorem value_set f x :
  x ∈ Dom f -> M f[x].
Proof.
  move => H.
  apply caps_set.
  apply not_empty.
  have x_ : M x by is_set.
  move /(in_dom f x x_) : H => [y [y_ xy_f]].
  exists y; apply in_cls => //.
Qed.

Goal forall x, M x -> ⊓ (Single x) = x.
Proof.
  move => x x_.
  equal => i.
  split => [H|H]; have i_ :  M i by is_set.
  + move /(in_caps (Single x) i i_) : H.
    apply.
    apply single_refl => //.
  + apply in_caps => //.
    move => y y_xx.
    have y_ : M y by is_set.
    move /(in_single x y y_) : y_xx -> => //.
Qed.  



Theorem in_value f x y (y_ : M y):
  Un f -> x ∈ Dom f -> <|x, y|> ∈ f <-> y = f[x].
Proof.
  move => unf x_domf.
  have H : forall z, M z -> <|x,z|> ∈ f -> z = f[x].
    move => z z_ zx_f.
    equal => i.
    split => [iz|i_fx]; have i_ : M i by is_set.
    - rewrite in_cls => //.
      move => j Hj.
      have j_ : M j by is_set.
      move /(in_cls _ j j_) : Hj => xj_f.
      suff yj : z = j.
        by subst z.
      apply unf with (x := x) => // ; is_set.
    - move /(in_cls _ i i_) : i_fx.
      apply.
      apply in_cls => //.
- split => [xy_f|y_fx].
  + apply H => //.
  + subst y.
    have x_ : M x by is_set.
    case /(in_dom f x x_) : x_domf => [z [z_ xz_f]].
    by move : (H z z_ xz_f) <-.
Qed.


Theorem value_in f x :
  Un f -> x ∈ Dom f -> <|x, f[x]|> ∈ f.
Proof.
  move =>  unf x_domf.
  have x_ : M x by is_set.
  have H0 : exists y, M y /\ <|x,y|> ∈ f.
    move /(in_dom f x x_) : x_domf  => [y [y_ xy_f]].
    by exists y.
  move : H0 => [y [y_ xy_f]].
  suff y_fx : y = f[x].
    by subst y.
  apply in_value => //.
Qed.  







    





    












 