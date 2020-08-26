Require Export Operations.


Axiom B5 :
  forall X, exists Z, forall u v, M u -> M v -> (<|u,v|>) ∈ Z <-> u ∈ X.

Axiom EvenPermute :
  forall X, exists Z, forall u v w, M u -> M v -> M w ->
  <| <|u,v|> , w |> ∈ Z <-> <| <|v,w|> , u |> ∈ X.

Axiom OddPermute :
  forall X, exists Z, forall u v w, M u -> M v -> M w ->
  <| <|u,v|> , w |> ∈ Z <-> <| <|u,w|> , v |> ∈ X.



Theorem Existance (P : Class -> Prop) :
  exists Z, forall x, M x -> x ∈ Z <-> P x.
Admitted.


Theorem welldefine_product X Y :
  exists  !U, forall u, M u -> 
  u ∈ U <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ X /\ y ∈ Y.
Proof.
  specialize (Existance (fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ X /\ y ∈ Y)) as H.
  induction H as [U H].
  exists U.
  apply (conj H).
  intros U_ H_.
  apply equal => i.  
  split => [iU | iU_].
  + assert (i_ : M i) by (by exists U).
    rewrite (H_ i i_).
    by rewrite <- (H i i_) .
  + assert (i_ : M i) by (by exists U_)      .
    rewrite (H i i_).
    by rewrite <- (H_ i i_).      
Qed.

Axiom Product : Class -> Class -> Class.
Notation "X × Y" := (Product X Y) (at level 10).
Axiom product :
  forall X Y u, u ∈ (X × Y) <-> 
  exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ X /\ y ∈ Y.

Definition Sq X := X × X.
Notation "X ²" := (Sq X)(at level 1).

Definition Rel X := X ⊆ V².

Axiom Power : Class -> Class.
Notation "℘ X" := (Power X)(at level 10).  
Axiom power :
  forall X x, x  ∈ (℘ X) <-> x ⊆ X.

Axiom Union : Class -> Class.
Notation "⊔ X" := (Union X)(at level 10).
Axiom union :
  forall X x, x ∈ (⊔X) <-> exists y, x ∈ y /\ y ∈ X.

Axiom ID : Class.
Axiom id :
  forall u, u ∈ ID <-> exists x, u = <|x,x|> .

Axiom Comprehension : (Class -> Prop) -> Class.
Notation "{| P |}"  := (Comprehension P) (at level 10).
Axiom comprehension :
  forall P u, M u -> u ∈ ({|P|}) <-> P u.

Definition Inverse U :=
  {| fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ <|y,x|> ∈ U |} .
Notation "X ⁰" := (Inverse X) (at level 1).  
Theorem inverse {U} :
    forall u, M u -> u ∈ U⁰ <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ <|y,x|> ∈ U.
Proof.
  intros u u_.
  by rewrite comprehension.
Qed.

Definition Ran U :=
  {| fun y => exists x, M x /\ <|x,y|> ∈ U |}.
Theorem ran U :
  forall y, M y -> y ∈ (Ran U) <-> exists x, M x /\ <|x,y|> ∈ U.
Proof.
  intros y y_.
  by rewrite comprehension.  
Qed.


Theorem dom_ran X :
  Ran X = Dom X ⁰.
Proof.
  apply equal => x.
  split => [H | H].
  + assert (x_ : M x) by (by exists (Ran X)).
    apply (ran X x x_) in H.
    apply dom.
    apply x_.
    induction H as [y H].
    induction H as  [y_ yx_X].
    exists y.
    apply (conj y_).
    apply inverse.
    apply nop_set.
    by exists x; exists y.
  + assert (x_ : M x) by (by exists (Dom X ⁰)).
    apply dom in H.
    apply ran.
    done.
    induction H as [y H].
    induction H as [y_ H].
    apply inverse in H.
    induction H as [x1]; induction H as [y1].
    induction H as [x1_]; induction H as [y1_].
    induction H as [xyxy yx_X].
    apply (OP_eq x y x1 y1 x_ y_ x1_ y1_) in xyxy.
    induction xyxy; subst x1 y1.
    by exists y.
    apply nop_set.
    done.
Qed.

Axiom U :
    forall x, M x -> exists y, M y /\ 
    (forall u, M u -> u ∈ y <-> exists v, M v /\ u ∈ v /\ v ∈ x).

Theorem union_set {X} {X_ : M X} :
      M (⊔ X).
Proof.
  specialize (U X X_) as H.
  induction H as [Y H].
  induction H as [Y_ H].
  inversion Y_ as [U HU].
  assert (YX : Y = ⊔ X).
  + apply equal => i.
    split => [iY | iX] .
    - assert (i_ : M i) by (by exists Y).
      apply union.
      specialize (H i i_).      
      apply H in iY.
      induction iY as [y Hy].
      induction Hy as [y_ Hy].
      by exists y.
    - assert (i_ : M i) by (by exists (⊔ X)) .
      apply union in iX.
      specialize (H i i_).
      rewrite H.
      induction iX as [y Hy].
      exists y.
      split.
      exists X.
      apply Hy.
      done.
  + rewrite <- YX.
    by exists U.
Qed.

Theorem union_nop x y (x_ : M x) (y_ : M y):
    ⊔ (NOP x y) = x ∪ y.
Proof.
  apply equal => i.
  rewrite union.
  rewrite cup.
  split => [H | H].
  + induction H as [u H].
    induction H as [iu u_xy].
    assert (u_ : M u) by (by exists (NOP x y)).
    apply (Pair x y u x_ y_ u_) in u_xy.
    induction u_xy as [ux | uy].
    - apply equal in ux.
      rewrite ux in iu.
      by apply or_introl.
    - apply equal in uy.
      rewrite uy in iu.
      by apply or_intror.
 + induction H as [ix | iy].
    - exists x.
      apply (conj ix).      
      apply (Pair x y x x_ y_ x_).
      apply or_introl.
      by apply equal.
    - exists y.
      apply (conj iy).
      apply (Pair x y y x_ y_ y_).
      apply or_intror.
      by apply equal.
Qed.

Theorem cup_set x y (x_ : M x) (y_ : M y):
      M (x ∪ y).
Proof.
  rewrite <- (union_nop x y x_ y_).
  assert (xy_ : M (NOP x y)) by (apply nop_set).
  apply (@union_set (NOP x y) xy_).
Qed.

Theorem union_empty :
    ⊔ ∅ = ∅.
Proof.
  apply equal => i.
  induction empty as [_ emp].
  rewrite union.
  split => [H | H]    .
  + induction H as [y H].
    specialize (emp y).
    induction H as [_ H].
    case (emp H).
  + specialize (emp i).
    case (emp H).
Qed.

Theorem union_single x (x_ : M x):
    ⊔ (Single x) = x.
Proof.
  apply equal => i.
  rewrite union.
  assert (x_xx : x ∈ (Single x)).
  apply (Pair x x x x_ x_ x_).
  by apply or_introl.
  split => [H | H].
  + induction H as [x1 H].
    induction H as [iX1 H].
    apply in_single in H.
    by apply equal in H; subst.
    by exists (Single x).
    exact x_.
  + exists x.
    apply (conj H x_xx).
Qed.

Theorem union_op x y (x_ : M x) (y_ : M y) :
    ⊔ (<|x,y|>) = NOP x y.
Proof. 
  apply equal => i.
  rewrite union.
  split => [H | H].
  + induction H as [u H].
    induction H as [iu uxy].
    apply op in uxy.
    apply Pair.
    apply x_.
    apply y_.
    by exists u.
    induction uxy.
    - rewrite H in iu.
      apply Pair in iu.
      apply (@or_elim (i ≡ x)) in iu.
      by apply or_introl.
      apply x_ .
      apply x_.
      by exists (Single x).
    - rewrite H in iu.
      apply Pair in iu.
      exact iu.
      apply x_.
      apply y_.
      by exists (NOP x y).
    - apply x_   .
    - apply y_.
    - by exists (<|x,y|>) .
  + exists (NOP x y).
    apply (conj H).
    apply Pair.
    apply nop_set.
    apply nop_set.
    apply nop_set.
    apply or_intror.
    by apply equal.
Qed.

Axiom W :
  forall x, M x -> exists y, M y /\
  (forall u, M u -> (u ∈ y <-> u ⊆ x)).

Theorem  Power_set x (x_ : M x) :
    M (℘ x).
Proof.
  specialize (W x x_) as H.
  induction H as [y H].
  induction H as [y_ H].
  inversion y_ as [U HU].
  assert (y_px : y = ℘ x).
  + apply equal => i.        
    split => [H1 | H1].
    - assert (i_ : M i) by (by exists y).
      apply power.
      specialize (H i i_).
      by apply H in H1.
    - assert (i_ : M i) by (by exists (℘ x)).
      apply power in H1.
      by apply (H i i_) in H1.
  + by rewrite <- y_px.
Qed.

Axiom S :
    forall x Y, M x -> exists z, M z /\
    (forall u, M u -> u ∈ z <-> u ∈ x /\ u ∈ Y).

Theorem cap_set x y (x_ : M x)  :
      M (x ∩ y).
Proof.
  specialize (S x y x_) as H.
  induction H as [XY H].
  induction H as [XY_ H].
  inversion XY_ as [U HU].
  assert (XY_xy : XY = x ∩ y ).
  + apply equal => i.
    rewrite cap.
    split => [iXY | ixiy].
    - assert (i_ : M i) by (by exists XY).
      specialize (H i i_).
      by apply H in iXY.
    - assert (i_ : M i) by (inversion ixiy; by exists x).
      by rewrite (H i i_).
  + by rewrite <- XY_xy.
Qed.

Theorem subset_set x y (x_ : M x) :
    y ⊆ x -> M y.
Proof.
  intro H.
  specialize (cap_set x y x_) as xy_.
  assert (y_xy : y = x ∩ y).
  + apply equal => i.
    rewrite cap.    
    split => [iy | ixiy].
    - by specialize (H i iy).
    - apply ixiy.
  + by rewrite y_xy.
Qed         .



         









  


  




    
  
    








    

