Require Export Functions.


Axiom Replacement :
  forall f X, M X ->  Un f -> M (Image f X).  




        

Theorem cap_set X Y (X_ : M X)  :
    M (X ∩ Y).
Proof.
  pose (fun p => exists x, p = <|x,x|> /\ x ∈ X /\ x ∈ Y) as H0.
  pose ({| H0 |}) as f.
  assert (Unf : Un f).
  + intros x y z x_ y_ z_ xy_f yz_f.
    apply (classify H0) in xy_f.
    induction xy_f as [a]; induction H as [xy_aa]; induction H as [aX _].
    assert (a_ : M a) by (by exists X).
    apply (OP_eq x y a a x_ y_ a_ a_) in xy_aa; induction xy_aa. subst a.
    apply (classify H0) in yz_f.
    induction yz_f as [a]; induction H as [yz_aa]; induction H as [aX_ _].
    assert (a__ : M a) by (by exists X).
    apply (OP_eq x z a a x_ z_ a__ a__) in yz_aa; induction yz_aa. subst a.
    by subst x.
    by apply op_set.
    by apply op_set.
  + assert (H : X ∩ Y = Image f X).
    - apply equal => x.
      rewrite cap.      
      split => [H | H].
      * rewrite image.      
        unfold f.
        unfold H0.
        exists x.
        induction H as [xX xY] .
        assert (x_ : M x) by (by exists X).
        apply (conj x_).
        apply (conj xX).
        apply classify.
        apply (op_set x x x_ x_).
        by exists x.
        exists X.
        apply H.
      * assert (x_ : M x) by (by exists (Image f X)).
        apply image in H.      
        unfold f in H.
        unfold H0 in H.
        induction H as [x0]; induction H as[x0_]; induction H as [xX].
        apply (classify H0) in H.
        induction H as [x1]; induction H as [xx_xx]; induction H as [_ xY].
        assert (x1_ : M x1) by (by exists Y).
        apply (OP_eq x0 x x1 x1 x0_ x_ x1_ x1_) in xx_xx. induction xx_xx. subst x0 x1.
        done.
        by apply op_set.
        done.
    - rewrite H.
      by apply Replacement.
Qed.

Theorem sub_set x y (y_ : M y):
  x ⊆ y -> M x.
Proof.
  intro H.
  assert (y_xy : x = y ∩ x).
  + apply equal => i.
    rewrite cap.
    split => [iy |iyix].
    - apply (conj (H i iy)).
      apply (iy).      
    - apply iyix.
  + specialize (cap_set y x y_).
    by rewrite <- y_xy.
Qed.

Definition Separation X P :=
  {| fun x => x ∈ X /\ P x|}.
Notation "{: X | P :}" := (Separation X P) (at level 10).   

Theorem separation {X P x} :
  x ∈ ({: X | P :}) <-> x ∈ X /\ P x.
Proof.
  split => [H | H].
  + assert (x_ : M x) by (by exists ({: X | P :})) .
    by apply (classify (fun x => x ∈ X /\ P x)) in H.
  + assert (x_ : M x) by (by induction H; exists X).
    by apply (classify (fun x => x ∈ X /\ P x)).
Qed.

Theorem separation_sub X P :
  {: X | P:} ⊆ X.
Proof.
  intros x XP.
  apply separation in XP.
  apply XP.
Qed.    

Theorem separation_set X P :
  M X -> M ({: X | P :}).
Proof.
  intro X_.
  specialize (separation_sub X P) as H0.
  by apply sub_set in H0.
Qed.  



Definition Value f x :=
    {| fun i => forall y, M y -> <|x,y|> ∈ f -> i ∈ y|}.

Theorem value f x :
  Un f -> x ∈ Dom f -> <|x, Value f x|>  ∈ f /\ M (Value f x).
Proof.
  intros unf H.
  assert (x_ : M x) by (by exists (Dom f)).
  apply dom in H.
  induction H as [y]; induction H as [y_ xy_f].
  assert (y_fx : y = Value f x).
  + apply equal => i.
    split => [H | H].
    - assert (i_ : M i) by (by exists y).
      apply classify.
      apply i_.
      intros y0 y0_ xy0_f.
      specialize (unf x y y0 x_ y_ y0_ xy_f xy0_f).
      by rewrite unf in H.
    - assert (i_ : M i) by (by exists (Value f x)).
      move: H; rewrite classify.
      intro H.
      by apply (H y y_ xy_f).
      apply i_.
  + by rewrite <- y_fx.
  + done.
Qed.  

Theorem value_set f x :
    Un f -> x ∈ Dom f -> M (Value f x).
Proof.
  intros unf domf.
  by induction (value f x unf domf).
Qed.
  
  



Theorem dom_set x (x_ : M x):
    M (Dom x).
Proof.
  assert (H : (Dom x) ⊆ (⊔ ⊔ x)).
  + intros i H.
    assert (i_ : M i) by (by exists (Dom x)).
    apply union.
    exists (Single i).
    split.
    by apply single.
    apply union.
    apply dom in H.
    induction H as [j]; induction H as [j_].
    exists (<|i,j|>).
    split.
    - apply op.
      done.      
      done.
      by apply pairing_set.
      by apply or_introl.
    - done.
    - done.
  + apply (sub_set (Dom x) (⊔ ⊔ x)).
    by repeat apply union_set.
    done.
Qed.

Theorem ran_set x (x_ : M x) :
    M (Ran x).
Proof.
  assert (H : Ran x ⊆ ⊔ ⊔ x).
  + intros v H.    
    assert (v_ : M v) by (by exists (Ran x)).
    apply ran in H.
    induction H as [u]; induction H as [u_ uv_x].
    apply union.
    exists (Pairing u v).
    split.
    by apply couple.
    apply union.
    exists (<|u,v|>).
    split.
    apply couple.
    by apply pairing_set.
    by apply pairing_set.
    done.
    done.
  + apply (sub_set (Ran x) (⊔ ⊔ x)) .
    by repeat apply union_set.
    done.
Qed.

Theorem cup_set x y (x_ : M x) (y_ : M y):
  M (x ∪ y).
Proof.
  assert (H : (x ∪ y) ⊆ (⊔ (Pairing x y))).
  + intros i i_xy.
    assert (i_ : M i) by (by exists (x ∪ y)).
    apply union.
    apply cup in i_xy.
    induction i_xy as [ix | iy].
    - exists x.
      apply (conj ix) .
      apply (pairing x y x x_).
      by apply or_introl.
    - exists y.
      apply (conj iy).
      apply(pairing x y y y_).
      by apply or_intror.
  + apply (sub_set _ (⊔ (Pairing x y))).
    apply union_set.
    by apply pairing_set.
    done. 
Qed.    



  

Theorem product_set x y (x_ : M x) (y_ : M y) :
    M (x × y).
Proof.
  assert (H : (x × y) ⊆ (Power (Power (x ∪ y)))).
  + intros i i_xy.
    assert (i_ : M i) by (by exists (x × y)).
    apply power.
    done.
    intros j j_i.
    assert (j_ : M j) by (by exists i).
    apply power.
    done.
    intros k k_j.
    apply cup.
    apply product in i_xy.
    induction i_xy as [x0]; induction H as [y0].
    induction H as [x0_]; induction H as [y0_].
    induction H as [i_x0y0]; induction H as [x0x y0y].
    rewrite i_x0y0 in j_i.
    apply op in j_i.
    induction j_i as [j_xx | j_xy].
    - subst j.
      apply in_single in k_j.
      apply or_introl.
      by subst k.
      by exists (Single x0).
      done.
    - subst j.
      apply pairing in k_j.
      induction k_j as [kx | ky].
      * apply or_introl.
        by subst k.
      * apply or_intror.
        by subst k.
      * by exists (Pairing x0 y0).
    - done.
    - done.
    - done.
  + apply (sub_set _ (Power (Power (x ∪ y)))).
    repeat apply power_set.
    by apply cup_set.
    done.
Qed.    
      
Goal forall f, M (Dom f) -> M (Ran f) -> Rel f -> M f.
Proof.
  intros f domf_ ranf_ relf.
  assert (H : f ⊆ (Power (Power ((Dom f) ∪  (Ran f))))).
  + intros i i_f.
    assert (i_ : M i) by (by exists f).
    apply power.
    done.
    intros j j_i.
    apply power.
    by exists i.
    intros k k_j.
    apply cup.
    specialize (relf i i_f).
    apply product in relf.
    induction relf as [x]; induction H as[y].
    induction H as [x_]; induction H as [y_].
    induction H as [i_xy _].
    subst i.
    apply op in j_i.    
    induction j_i as [j_xx | j_xy].
    - subst j.
      apply in_single in k_j.
      subst k.
      apply or_introl.
      apply dom.
      done.
      by exists y.
      by exists (Single x).
      done.
    - subst j.
      apply pairing in k_j.
      induction k_j as [kx | ky].
      * subst k.
        apply or_introl.
        apply dom.
        done.
        by exists y.
      * subst k.
        apply or_intror.
        apply ran .
        done.
        by exists x.
      * by exists (Pairing x y) .
    - done.
    - done.
    - by exists (<|x,y|>).
  + apply (sub_set f  (Power (Power ((Dom f) ∪ (Ran f))))).
    repeat apply power_set.
    by apply cup_set.
    done.
Qed.

Goal forall x, M x -> forall f, Fnc f -> M (Image f x).
Proof.
  intros x x_ f fncf.
  apply Replacement.
  done.
  apply fncf.
Qed.  


Theorem caps_set X :
  X <> ∅ -> M (⊓ X).
Proof.
  intro not_empty.
  assert (ex_x : exists x, x ∈ X).
  + move : not_empty.
    apply contrapositive.
    rewrite <- allnot_notexists.
    intro H.
    apply DoubleNegative.
    apply equal => x.
    split => [h | h].
    - case (H x h).
    - assert (x_ : M x) by (by exists ∅).
      specialize (empty x x_) as emp.      
      case (emp h).
  + induction ex_x as [x xX].
    assert (H : ⊓ X ⊆ x).
    - intros i iX.
      assert (i_ : M i) by (by exists (⊓ X)).
      move : iX.
      rewrite caps.
      by apply.
      done.
    - apply (sub_set _ x).
      by exists X.
      done.
Qed.

Definition Inverse f :=
  {: (Ran f) × (Dom f) |
   fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ <|y,x|> ∈ f 
  :}.

Theorem inverse f u :
  u ∈ Inverse f <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ <|y,x|> ∈ f.
Proof.
  split => [H | H].
  + assert (u_ : M u) by (by exists (Inverse f)).
    apply separation in H.
    by induction H as [H H0].
  + induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [u_xy uf].
    subst u.
    apply separation.
    split.
    - apply product.
      exists x; exists y.
      refine (conj x_ (conj y_ _)).
      apply conj. done.
      split.
      * apply ran.
        done.
        by exists y.
      * apply dom.
        done.
        by exists x.
    - by exists x; exists y.
Qed.


Definition Un₁ X := Un X /\ Un (Inverse X).






    





    












 