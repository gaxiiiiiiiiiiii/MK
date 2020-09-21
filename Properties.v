Require Export Definitions.


Theorem couple x y (x_ : M x) (y_ : M y) :
    x ∈ (Pairing x y) /\ y ∈ (Pairing x y).
Proof.
  split.
  + apply (pairing x y x x_).
    by apply or_introl.
  + apply (pairing x y y y_).
    by apply or_intror.
Qed.
    



Theorem pairing_refl X Y (X_ : M X) (Y_ : M Y):
    (Pairing X Y) = (Pairing Y X).
Proof.
  apply equal.
  intros i.
  split => [H | H].
  + assert (i_ : M i)  by (by exists (Pairing X Y)).
    apply (pairing X Y i i_) in H.
    apply (pairing Y X i i_).
    by apply or_comm.
  + assert (i_ : M i)  by (by exists (Pairing Y X)).
    apply (pairing X Y i i_).
    apply (pairing Y X i i_) in H.
    by apply or_comm.  
Qed.        



 
Theorem in_single x X (x_ : M x) (X_ : M X):
  x ∈ (Single X) <-> x = X.
Proof.
  split => [H | H].
  + apply (pairing X X x x_) in H.
    by apply (@or_elim (x = X)) in H.
  + rewrite H.
    by apply single.
Qed.    


Theorem single_single :
  forall x y, M x -> M y -> ((Single x) = (Single y)) <-> (x = y).
Proof.
  intros x y x_ y_.
  split => [H | H].
  + specialize (single x x_) as x_xx.
    rewrite H in x_xx.
    by apply (in_single x y x_ y_) in x_xx.
  + by rewrite H.
Qed.  

Theorem pairing_single x y X (x_ : M x) (y_ : M y) (X_ : M X):
    (Pairing x y) = (Single X) <-> x = X /\ y = X.
Proof.
  split => [H | H].
  + specialize (couple x y x_ y_) as H0.
    rewrite H in H0.
    induction H0 as [x_X y_X].
    apply (in_single x X x_ X_) in x_X.
    by apply (in_single y X y_ X_) in y_X.
  + induction H as [xX yX].
    by subst x y.
Qed.

Theorem single_pairing X x y (X_ : M X) (x_ : M x) (y_ : M y) :
    (Single X) = (Pairing x y) -> x = X /\ y = X.
Proof.
  intro H.
  symmetry in H.
  by apply (pairing_single x y X x_ y_ X_) in H.
Qed.     




Theorem pairing_pairing x y X Y (x_ : M x) (y_ : M y) (X_ : M X) (Y_ : M Y) :
  (Pairing x y) = (Pairing X Y) <-> (x = X /\ y = Y) \/ (x = Y /\ y = X).
Proof.
  split => [H | H].
  + specialize (couple x y x_ y_) as H1.
    specialize (couple X Y X_ Y_) as H2.
    move: H1; rewrite H; intro H1.
    move: H2; rewrite <- H; clear H; intro H2.
    induction H1 as [x_XY y_XY].
    induction H2 as [X_xy Y_xy].
    apply (pairing X Y x x_) in x_XY.
    apply (pairing X Y y y_) in y_XY.
    apply (pairing x y X X_) in X_xy.
    apply (pairing x y Y Y_) in Y_xy.
    induction x_XY as [xX | xY].
    - subst X. 
      induction y_XY as [yX | yY].
      * subst y.
        induction Y_xy as [Yx | Yx].
          subst Y.
          by apply or_introl.
          subst Y.
          by apply or_introl.
      * subst Y.
        by apply or_introl.
    - subst Y.
      induction y_XY as [yX | yx].
      * subst X.
        by apply or_intror.
      * subst y.
        apply (@or_elim (X = x)) in X_xy.
        subst X.
        by apply or_introl.
  + induction H as [H | H].
    - induction H as [xX yY].
      by subst X Y.
    - induction H as [xY yX].
      subst X Y.
      by apply pairing_refl.
Qed.      


Theorem op x y i (x_ : M x) (y_ : M y) (i_ : M i):
  i ∈ <|x,y|> <-> i = (Single x) \/ i = (Pairing x y).
Proof.
  by rewrite pairing.
Qed.   





    

Theorem OP_eq x y X Y (x_ : M x) (y_ : M y) (X_ : M X) (Y_ : M Y) :
    (<|x,y|>) = (<|X,Y|>) <-> x = X /\ y = Y.
Proof.
  assert (xx_ : M (Single x)) by (by apply (pairing_set x x)).
  assert (xy_ : M (Pairing x y)) by (by apply (pairing_set x y)).
  assert (XX_ : M (Single X)) by (by apply (pairing_set X X)).
  assert (XY_ : M (Pairing X Y)) by (by apply (pairing_set X Y)).
  specialize (couple (Single x) (Pairing x y) xx_ xy_) as H1.
  specialize (couple (Single X) (Pairing X Y) XX_ XY_) as H2.
  induction H1 as [x_xOPy xy_xOPy].
  induction H2 as [X_XOPY XY_XOPY].
  unfold OP.
  split => [H | H].
  + rewrite H in x_xOPy.
    rewrite H in xy_xOPy.
    rewrite <- H in XY_XOPY.
    clear H.
    clear X_XOPY.
    apply  (pairing (Single x) (Pairing x y) (Pairing X Y)  XY_) in XY_XOPY.
    apply (pairing (Single X) (Pairing X Y) (Single x) xx_) in x_xOPy.
    apply (pairing (Single X) (Pairing X Y) (Pairing x y) xy_) in xy_xOPy.
    case (ExcludedMiddle (x = y)) as [xy | notxy].
    - subst y.
      induction xy_xOPy as [x_X | x_XY].
      * apply (single_single x X x_ X_) in x_X.
        apply (conj x_X).
        subst X.
        apply (@or_elim ((Pairing x Y) = (Single x)))in XY_XOPY.
        apply (pairing_single x Y x x_ Y_ x_) in XY_XOPY.
        symmetry.
        apply XY_XOPY.
      * apply (single_pairing x X Y x_ X_ Y_ ) in x_XY.
        induction x_XY as [Xx Yx].
        by symmetry in Yx.
    - induction xy_xOPy as [xy_X | xy_XY].
      * apply (pairing_single x y X x_ y_ X_) in xy_X.
        induction xy_X.
        subst y.
        case (notxy H).
      * apply (pairing_pairing x y X Y x_ y_ X_ Y_) in xy_XY.
        induction xy_XY as [H | H].
          by induction H as [R L].
          induction H as [xY yX].
          subst X Y.
          induction x_xOPy as [x_y | x_yx].
            apply (single_single x y x_ y_) in x_y.
            apply (conj x_y).
            by symmetry.
            apply (single_pairing x y x x_ y_ x_) in x_yx.
            induction x_yx as [y_x _].
            by subst y.
 + induction H as [xX yY].
   by subst X Y.
Qed.



Theorem op_set X Y (X_ : M X) (Y_ : M Y) :
  M <|X,Y|>.
Proof.
  apply pairing_set.
  by apply pairing_set.
  by apply pairing_set.
Qed.  

Theorem cap_comm x y :
  x ∩ y = y ∩ x.
Admitted.

Theorem cup_comm x y :
  x ∪ y = y ∪ x.
Admitted.

Theorem cap_assoc x y z :
  (x ∩ y) ∩ z = x ∪ (y ∪ z).
Admitted.

Theorem cup_assoc x y z :
  (x ∪ y) ∪ z = x ∪ (y ∪ z) .
Admitted.

Theorem union_pairing x y (x_ : M x) (y_ : M y):
  x ∪ y = ⊔ (Pairing x y).
Proof.
  apply equal => i.
  split => [H | H].
  + assert (i_ : M i) by (by exists (x ∪ y)) .
    apply cup in H.
    apply union.
    induction H as [ix | iy].
    - exists x.
      apply (conj ix).
      apply (pairing x y x).
      done.
      by apply or_introl.
    - exists y.
      apply (conj iy).
      apply (pairing x y y).
      done.
      by apply or_intror.
  + apply union in H.
    induction H as[u].
    induction H as [iu u_xy].
    apply pairing in u_xy.
    apply cup.
    induction u_xy as [ux | uy].
    - subst u.
      by apply or_introl.
    - subst u.
      by apply or_intror.
    - by exists (Pairing x y).
Qed.

Theorem caps_pairing x y (x_ : M x) (y_ : M y) :
  x ∩ y = ⊓ (Pairing x y).
Proof.
  apply equal => i.
  split => [H | H].
  + assert (i_ : M i) by (by exists (x ∩ y)).
    apply cap in H.
    induction H as [ix iy].
    apply caps.
    done.
    intros u Hu.
    apply pairing in Hu.
    induction Hu as [ux | uy].
    - by subst u.
    - by subst u.
    - by exists (Pairing x y).
  + assert (i_ : M i) by (by exists (⊓ (Pairing x y))).
    move : H.
    rewrite caps.
    intro.
    apply cap.
    split.
    - apply (H x).
      apply pairing.
      done.
      by apply or_introl.
    - apply (H y).
      apply pairing.
      done.
      by apply or_intror.
    - done.
Qed.









    



    

 



     



 




  






