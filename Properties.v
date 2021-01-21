Require Export Definitions.


Theorem pair_refl x y (x_ : M x) (y_ : M y) :
    x ∈ (Pair x y) /\ y ∈ (Pair x y).
Proof.
  split; rewrite in_pair //; [left|right] => //.
Qed.
    



Theorem pair_comm X Y (X_ : M X) (Y_ : M Y):
    (Pair X Y) = (Pair Y X).
Proof.
  apply Equal => i.
  split => [H | H];  have i_ : M i by is_set.
  + move : H; rewrite !in_pair //; case => [iX|iY]; [right|left] => //=.
  + move : H; rewrite !in_pair //; case => [iY|iX]; [right|left] => //=.
Qed.        

Theorem single_refl x (x_ : M x) :
    x ∈ Single x.
Proof.
  apply in_single => //.
Qed.      

Theorem single_single x y (x_ : M x) (y_ : M y):
  ((Single x) = (Single y)) <-> (x = y).
Proof.
  split => [H | H].
  + move : (single_refl x x_).
    rewrite H.
    move /in_single.
    auto.
  + by rewrite H.
Qed.  

Theorem pair_single x y X (x_ : M x) (y_ : M y) (X_ : M X):
    (Pair x y) = (Single X) <-> x = X /\ y = X.
Proof.
  split => [H | H].
  + move : (pair_refl x y x_ y_).
    rewrite H.
    case; rewrite !in_single => //.
  + by move : H => [xX yX]; subst x y.
Qed.

Theorem single_pair X x y (X_ : M X) (x_ : M x) (y_ : M y) :
    (Single X) = (Pair x y) -> x = X /\ y = X.
Proof.
  intro H.
  symmetry in H.
  by apply (pair_single x y X x_ y_ X_) in H.
Qed.     




Theorem pair_pair x y X Y (x_ : M x) (y_ : M y) (X_ : M X) (Y_ : M Y) :
  (Pair x y) = (Pair X Y) <-> (x = X /\ y = Y) \/ (x = Y /\ y = X).
Proof.
  split => [H | [[xX yY]|[xY yX]]].
  + move : (pair_refl x y x_ y_) => [x_xy y_xy].
    move : (pair_refl X Y X_ Y_) => [X_XY Y_XY].
    rewrite H in x_xy.
    rewrite H in y_xy.
    rewrite -H in X_XY.
    rewrite -H in Y_XY.
    move /(in_pair X Y x x_) : x_xy => [xX | xY]; [left|right]; split => // ; subst x.
    - move /(in_pair X Y y y_):  y_xy => [yX | yY]; subst y => //.
      move /(in_single) : Y_XY.
      by symmetry; auto.
    - move /(in_pair X Y y y_):  y_xy => [yX | yY]; subst y => //.
      move /in_single : X_XY.
      by symmetry; auto.
  + by subst x y.
  + subst x y.
    apply pair_comm => //.
Qed.    



Theorem in_orderd x y i (x_ : M x) (y_ : M y) (i_ : M i):
  i ∈ <|x,y|> <-> i = (Single x) \/ i = (Pair x y).
Proof.
  by rewrite in_pair.
Qed.   





    

Theorem orderd_eq x y X Y (x_ : M x) (y_ : M y) (X_ : M X) (Y_ : M Y) :
    (<|x,y|>) = (<|X,Y|>) <-> x = X /\ y = Y.
Proof.
  have xx_ : M (Single x) by apply single_set.
  have xy_ : M (Pair x y) by apply (pair_set x y).
  have XX_ : M (Single X) by apply single_set.
  have XY_ : M (Pair X Y) by apply (pair_set X Y).
  move : (pair_refl (Single x) (Pair x y) xx_ xy_) => [xx_xOPy xy_xOPy].
  move : (pair_refl (Single X) (Pair X Y) XX_ XY_) => [_ XY_XOPY].
  unfold Orderd.
  split => [H | [xX yY]].
  + rewrite H in xx_xOPy.
    rewrite H in xy_xOPy.
    rewrite <- H in XY_XOPY.
    clear H.
    move /(in_pair _ _ _ XY_) : XY_XOPY => H1.
    move /(in_pair _ _ _ xx_) : xx_xOPy => H2.
    move /(in_pair _ _ _ xy_) : xy_xOPy => H3.
    case H1 => {H1} [H1|H1].    
    - case /(pair_single X Y x X_ Y_ x_ ) : H1 => Xx Yx; subst X Y; split => //.
      case H3 => [H|H]; case /pair_single : H; auto.
    - case /(pair_pair X Y x y X_ Y_ x_ y_) : H1 => [[Xx Yy]|[Xy Yx]]; subst x y => //.
      case H2 => [YY_XX | YY_XY].
      * move /(single_single Y X Y_ X_) : YY_XX; split => //.
      * move /(single_pair Y X Y Y_ X_ Y_) : YY_XY => [XY _]; subst X => //.
  + by subst x y.
Qed.    
       
Ltac equal := rewrite -Equal.

Theorem cap_comm x y :
  x ∩ y = y ∩ x.
Proof.
  equal => i.
  rewrite !in_cap.
  split => [[l r]|[l r]]; split => //.
Qed.    

Theorem cup_comm x y :
  x ∪ y = y ∪ x.
Proof.
  equal => i.
  rewrite !in_cup.
  split => [[ix|iy]|[iy|ix]]; [right|left|right|left] => //.
Qed.

Theorem cap_assoc x y z :
  (x ∩ y) ∩ z = x ∩  (y ∩ z).
Proof.
  equal => i.
  rewrite !in_cap.
  split => [[[ix iy] iz] | [ix [iy iz]]] => //.
Qed.  

Theorem cup_assoc x y z :
  (x ∪ y) ∪ z = x ∪ (y ∪ z) .
Proof.
  equal => i; rewrite !in_cup.
  split => [[[ix | iy] | iz] | [ix | [iy | iz]]]; eauto.
Qed.

Theorem union_Pair x y (x_ : M x) (y_ : M y):
  x ∪ y = ⊔ (Pair x y).
Proof.
  equal => i; rewrite in_cup in_cups.
  split => [[ix | iy] | [xy [ixy xyxy]]]; have i_ : M i by is_set.
  + exists x; split => //.
    by apply in_pair => //; left.
  + exists y; split => //.
    by apply in_pair => //; right.
  + have xy_ : M xy  by is_set.
    move /(in_pair x y xy xy_) : xyxy => [Hx|Hy]; subst xy; [left|right] => //.
Qed.

Theorem caps_Pair x y (x_ : M x) (y_ : M y) :
  x ∩ y = ⊓ (Pair x y).
Proof.
  equal => i; rewrite in_cap.
  split => [[ix iy] | H]; have i_ : M i by is_set.
  + rewrite in_caps => // Y Yxy.
    have Y_ : M Y by is_set.
    case /(in_pair x y Y Y_) : Yxy => [Yx | Yy]; subst Y => //.
  + move /(in_caps _ i i_) : H => H.
    split; apply H; apply in_pair => //; [left|right] => //.  
Qed.









    



    

 



     



 




  






