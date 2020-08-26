Require Export Axioms.


Definition Single X := 
  Pairing X X.

Definition OP X Y:= Pairing (Single X) (Pairing X Y).
Notation "<| a , b , .. , d |>" := (OP .. (OP a b) .. d).

  
Definition InRel :=
  {|fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ y|}.

Theorem inrel u :
  u ∈ InRel <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ y.
Proof.
  split => [H | H].
  + assert (u_ : M u) by (by exists InRel).
    by move: H; apply classify.
  + induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [u_xy xy].
    apply classify.
    rewrite u_xy.
    apply pairing_set.
    by apply pairing_set.
    by apply pairing_set.
    by exists x; exists y.
Qed.

Definition Intersection X Y :=
  {|fun u => u ∈ X /\ u ∈ Y|}.
Notation "X ∩ Y" := (Intersection X Y)  (at level 10).

Theorem cap X Y u :
    u ∈ X ∩ Y <->  u ∈ X /\ u ∈ Y.
Proof.
  split => [H | H].
  + assert (u_ : M u) by (by exists (X ∩ Y)).
    by move: H ; rewrite classify.
  + rewrite classify.
    auto.
    by induction H; exists X.
Qed.   



Definition Comple X := 
  {| fun x => ~ x ∈ X|}.
Notation "X ^c" := (Comple X)(at level 10).

Theorem comple X x (x_ : M x):
    x ∈ X ^c <-> ~ x ∈ X.
Proof.
  by rewrite classify.
Qed.

Definition Cup X Y :=
    ((X ^c) ∩ (Y ^c)) ^c.
Notation "X ∪ Y" := (Cup X Y) (at level 10).    

Theorem cup X Y u (u_ : M u):
  u ∈ (X ∪ Y) <-> u ∈ X \/ u ∈ Y.
Proof.
  unfold Cup.
  rewrite (comple _ u u_).
  rewrite cap.
  repeat rewrite (comple _ u u_).
  rewrite DeMorgan_notand.
  repeat rewrite DoubleNegative.
  done.
Qed.


Definition Dom f :=
  {| fun x => exists y, M y /\ <|x,y|> ∈ f|}.

Theorem dom f x (x_ : M x):
  x ∈ Dom f <-> exists y, M y /\ <|x,y|> ∈ f.
Proof.
  by rewrite classify.
Qed.

Definition Ran f := 
  {|fun y => exists x, M x /\ <|x,y|> ∈ f|}.

Theorem ran f y (y_ : M y) :
  y ∈ Ran f <-> exists x, M x /\ <|x,y|> ∈ f.
Proof.
  by rewrite classify.
Qed.

Definition Diff X Y :=
  {| fun u => u ∈ X /\ ~ u ∈ Y|}.
Notation "X // Y"  := (Diff X Y) (at level 10).

Theorem diff X Y u :
  u ∈ X // Y <-> u ∈ X /\ ~ u ∈ Y.
Proof.
  split => [H | H].
  + assert (u_ : M u) by (by exists (X // Y)) .
    by move: H; rewrite classify.
  + assert (u_ : M u) by (by induction H; exists X).
    by rewrite classify.
Qed.



Definition Product X Y :=
  {| fun u => exists x y, u = <|x,y|> /\ x ∈ X /\ y ∈ Y|}.
Notation "X × Y" := (Product X Y) (at level 10).

Theorem product X Y u :
  u ∈ X × Y <-> exists x y, u = <|x,y|> /\ x ∈ X /\ y ∈ Y.
Proof.
  split => [H | H].
  + assert (u_ : M u) by (by exists (X × Y)).
    by move: H; apply classify.
  + rewrite classify.
    exact H.
    induction H as [x]; induction H as [y].
    induction H as [u_xy]; induction H as[xX yY].
    assert (x_ : M x) by (by exists X).
    assert (y_ : M y) by (by exists Y).
    rewrite u_xy.
    apply pairing_set.
    by apply pairing_set.
    by apply pairing_set.
Qed.


Definition Sq X := X × X.
Notation "X ²" := (Sq X)(at level 1).

Definition Rel X := X ⊆ V².

Definition Power X :=
  {| fun x => x ⊆ X|}.
Theorem power X x {x_ : M x}:
    x ∈ (Power X) <-> x ⊆ X.
Proof.
  by rewrite classify.
Qed.

Definition Inverse f :=
  {| fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ <|y,x|> ∈ f|}.
Notation "f ¹"  := (Inverse f) (at level 5).

Theorem inverse f u (u_ : M u) :
  u ∈ f¹ <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ <|y,x|> ∈ f.
Proof.
  by rewrite classify.
Qed.

Definition Union X :=
  {| fun x => exists Y, x ∈ Y /\ Y ∈ X|}.
Notation "⊔ X" := (Union X) (at level 10).

Theorem union X x (x_ : M x):
  x ∈ ⊔ X <-> exists Y, x ∈ Y /\ Y ∈ X.
Proof.
  by apply classify.
Qed.

(****************************)
(* next union_set power_set cup_set sub_set *)

  











Theorem pair_ x y (x_ : M x) (y_ : M y) :
    x ∈ (NOP x y) /\ y ∈ (NOP x y).
Proof.
  split.
  + apply (Pair x y x x_ y_ x_).
    by apply or_introl.
  + apply (Pair x y y x_ y_ y_).
    by apply or_intror.
Qed.         



Theorem nop_refl X Y :
    (NOP X Y) ≡ (NOP Y X).
Proof.
  specialize (nop X Y) as H1.  
  specialize (nop Y X) as H2.
  induction H1 as [L1 | R1].
  + induction L1 as [notXY_ L1].
    apply DeMorgan_notand in notXY_.
    induction H2 as [L2 | R2].
    - induction L2 as[_ L2].
      by rewrite L1; rewrite L2.
    - induction R2 as [Y_ R2]; induction R2 as[X_ _].
      case (notXY_ (conj X_ Y_)).
  + induction R1 as [X_ R1]; induction R1 as[Y_ R1].
    induction H2 as [L2 | R2].
    - induction L2 as [notXY_ _].
      apply DeMorgan_notand in notXY_.
      case (notXY_ (conj Y_ X_)).
    - induction R2 as [_ R2]; induction R2 as [_ R2].
      intro i.
      split => [H | H].
      * assert (i_ : M i) by (by exists (NOP X Y)).
        apply (R1 i i_) in H.
        rewrite (Pair Y X i Y_ X_ i_).
        by rewrite or_comm.
      * assert (i_ : M i) by (by exists (NOP Y X)).
        apply (R2 i i_) in H.
        rewrite (Pair X Y i X_ Y_ i_).
        by rewrite or_comm.
Qed.        

Definition Single X := 
  NOP X X.

Theorem single :
  forall x, M x -> x ∈ (Single x).
Proof.
  intros x x_.
  apply (Pair x x x x_ x_ x_).
  apply or_introl.
  by apply equal.
Qed.  

Theorem in_single x X (x_ : M x) (X_ : M X):
  x ∈ (Single X) <-> x ≡ X.
Proof.
  split => [H | H].
  + apply (Pair X X x X_ X_ x_) in H.
    by induction H.
  + apply equal in H; subst X.
    apply single.
    apply x_.
Qed.    


Theorem single_single :
  forall x y, M x -> M y -> ((Single x) ≡ (Single y)) <-> (x ≡ y).
Proof.
  intros x y x_ y_.
  split => [H | H].
  + specialize (single x x_) as x_xx.
    apply equal in H.
    rewrite H in x_xx.
    apply (Pair y y x y_ y_ x_) in x_xx.
    by induction x_xx.
  + apply equal in H.
    rewrite H.
    by apply equal.
Qed.  

Theorem nop_single x y X (x_ : M x) (y_ : M y) (X_ : M X):
    (NOP x y) ≡ (Single X) <-> x ≡ X /\ y ≡ X.
Proof.
  split => [H | H].
  + apply equal in H.
    specialize (pair_ x y x_ y_) as xy_X.
    move: xy_X; rewrite H; clear H; intro H.
    induction H as [xX yX].
    apply (in_single x X x_ X_) in xX.
    apply (in_single y X y_ X_) in yX.
    done.    
  + induction H as [xX yX].
    apply equal in xX; subst X.
    apply equal in yX; subst y.
    by apply equal. 
Qed.

Theorem single_nop X x y (X_ : M X) (x_ : M x) (y_ : M y) :
    (Single X) ≡ (NOP x y) -> x ≡ X /\ y ≡ X.
Proof.
  intro H.
  apply equal_sym in H.
  by apply (nop_single x y X x_ y_ X_) in H.
Qed.     




Theorem nop_nop x y X Y (x_ : M x) (y_ : M y) (X_ : M X) (Y_ : M Y) :
  (NOP x y) ≡ (NOP X Y) <-> (x ≡ X /\ y ≡ Y) \/ (x ≡ Y /\ y ≡ X).
Proof.
  split => [H | H].
  + specialize (pair_ x y x_ y_) as H1.
    specialize (pair_ X Y X_ Y_) as H2.
    apply equal in H.
    move: H1; rewrite H; intro H1.
    move: H2; rewrite <- H; clear H; intro H2.
    induction H1 as [x_XY y_XY].
    induction H2 as [X_xy Y_xy].
    apply (Pair X Y x X_ Y_ x_) in x_XY.
    apply (Pair X Y y X_ Y_ y_) in y_XY.
    apply (Pair x y X x_ y_ X_) in X_xy.
    apply (Pair x y Y x_ y_ Y_) in Y_xy.
    induction x_XY as [xX | xY].
    - apply equal in xX; subst X. 
      induction y_XY as [yX | yY].
      * apply equal in yX; subst y.
        induction Y_xy as [Yx | Yx].
          apply equal in Yx; subst Y.
          by apply or_introl.
          apply equal in Yx; subst Y.
          by apply or_introl.
      * apply equal in yY; subst Y.
        by apply or_introl.
    - apply equal in xY; subst Y.
      induction y_XY as [yX | yx].
      * apply equal in yX; subst X.
        by apply or_intror.
      * apply equal in yx; subst y.
        apply (@or_elim (X ≡ x)) in X_xy.
        apply equal in X_xy; subst X.
        by apply or_introl.
  + induction H as [H | H].
    - induction H as [xX yY].
      apply equal in xX; subst X.
      apply equal in yY; subst Y.
      apply equal_refl.
    - induction H as [xY yX].
      apply equal in xY; subst Y.
      apply equal in yX; subst X.
      apply nop_refl.
Qed.      




Definition OP X Y :=
  NOP (Single X) (NOP X Y).
(* Notation "<| X , Y |>"  := (OP X Y)(at level 10). *)
Notation "<| a , b , .. , d |>" := (OP .. (OP a b) .. d).

Theorem op x y i (x_ : M x) (y_ : M y) (i_ : M i):
  i ∈ <|x,y|> <-> i = (Single x) \/ i = (NOP x y).
Proof.
  rewrite Pair.
  by repeat rewrite equal.
  apply nop_set.
  apply nop_set.
  apply i_.
Qed.   





    

Theorem OP_eq x y X Y (x_ : M x) (y_ : M y) (X_ : M X) (Y_ : M Y) :
    (<|x,y|>) = (<|X,Y|>) <-> x = X /\ y = Y.
Proof.
  assert (xx_ : M (Single x)) by (apply (nop_set x x)).
  assert (xy_ : M (NOP x y)) by (apply (nop_set x y)).
  assert (XX_ : M (Single X)) by (apply (nop_set X X)).
  assert (XY_ : M (NOP X Y)) by (apply (nop_set X Y)).
  specialize (pair_ (Single x) (NOP x y) xx_ xy_) as H1.
  specialize (pair_ (Single X) (NOP X Y) XX_ XY_) as H2.
  induction H1 as [x_xOPy xy_xOPy].
  induction H2 as [X_XOPY XY_XOPY].
  unfold OP.
  repeat split => [H | H].
  + rewrite H in x_xOPy.
    rewrite H in xy_xOPy.
    rewrite <- H in XY_XOPY.
    clear H.
    clear X_XOPY.
    apply  (Pair (Single x) (NOP x y) (NOP X Y)  xx_ xy_ XY_) in XY_XOPY.
    apply (Pair (Single X) (NOP X Y) (Single x) XX_ XY_ xx_) in x_xOPy.
    apply (Pair (Single X) (NOP X Y) (NOP x y) XX_ XY_ xy_) in xy_xOPy.
    case (ExcludedMiddle (x = y)) as [xy | notxy].
    - subst y.
      induction xy_xOPy as [x_X | x_XY].
      * apply (single_single x X x_ X_) in x_X.
        apply equal in x_X.
        apply (conj x_X).
        subst X.
        apply (@or_elim ((NOP x Y) ≡ (Single x)))in XY_XOPY.
        apply (nop_single x Y x x_ Y_ x_) in XY_XOPY.
        symmetry.
        apply equal.
        apply XY_XOPY.
      * apply (single_nop x X Y x_ X_ Y_ ) in x_XY.
        induction x_XY as [Xx Yx].
        apply equal_sym in Xx.
        apply equal in Xx.
        apply equal in Yx.
        by symmetry in Yx.
    - induction xy_xOPy as [xy_X | xy_XY].
      * apply (nop_single x y X x_ y_ X_) in xy_X.
        induction xy_X.
        apply equal in H; apply equal in H0.
        subst y.
        case (notxy H).
      * apply (nop_nop x y X Y x_ y_ X_ Y_) in xy_XY.
        induction xy_XY as [H | H].
          induction H as [R L].
          by apply equal in R; apply equal in L.
          induction H as [xY yX].
          apply equal in xY; apply equal in yX; subst X Y.
          induction x_xOPy as [x_y | x_yx].
            apply (single_single x y x_ y_) in x_y.
            apply equal in x_y.
            apply (conj x_y).
            by symmetry.
            apply (single_nop x y x x_ y_ x_) in x_yx.
            induction x_yx as [y_x _].
            split.
            apply equal.
            by apply equal_sym.
            by apply equal.
 + induction H as [xX yY].
   by subst X Y.
Qed.   




      

(*******************)

Theorem equal_inclusion (X Y : Class) :
    X ≡ Y <-> ((X ⊆ Y) /\ (Y ⊆ X)).
Proof.
  rewrite /Equal /Inclusion.
  split => [H | H].
  + split.
    intro Z.
    apply H.
    intro Z.
    apply H.
  + induction H as [L R].
    intro Z.
    apply (conj (L Z) (R Z)).
Qed.

Theorem equal_refl (X : Class) :
    X ≡ X.
Proof.
  done.
Qed.

Theorem equal_sym (X Y : Class) :
  X ≡ Y -> Y ≡ X.
Proof.
  rewrite /Equal.
  intros H Z.
  by induction (H Z).
Qed.

Theorem equal_trans (X Y Z : Class) :
  X ≡ Y -> Y ≡ Z -> X ≡ Z.
Proof.    
  intros XY YZ z.
  specialize (XY z).
  specialize (YZ z).
  rewrite XY.
  by rewrite YZ.
Qed. 




    



    

    

    


  








