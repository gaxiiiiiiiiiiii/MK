Require Export Composition.




Definition Irr R A :=
  Rel R /\ forall x, x ∈ A -> ~ <|x,x|> ∈ R.

Definition Tr R A :=
  Rel R /\ 
  forall x y z, x ∈ A /\ y ∈ A /\ z ∈ A /\ 
  <|x,y|> ∈ R /\ <|y,z|> ∈ R -> 
  <|x,z|> ∈ R.

Definition Part R A :=
  Tr R A /\ Irr R A.
  
Definition Con R A :=
  Rel R /\ 
  forall x y, x ∈ A /\ y ∈ A /\ x <> y -> 
  <|x,y|> ∈ R \/ <|y,x|> ∈ R.

Definition Tot R A :=
  Tr R A /\ Irr R A /\ Con R A.
  
Definition We R A :=
    Irr R A /\
    forall Y, Y ⊆ A /\ Y <> ∅ ->
    exists m, m ∈ Y /\ 
    forall y, y ∈ Y /\ y <> m -> <|m,y|> ∈ R /\ ~ <|y,m|> ∈ R.

Definition sim  f W1 W2 :=
  exists x1 x2 r1 r2, 
  M x1 /\ M x2 /\ M r1 /\ M r2 /\
  Rel r1 /\ Rel r2 /\ W1 = <|r1,x1|> /\ W2 = <|r2,x2|> /\
  Rel f /\ Un₁ f /\ Dom f = x1 /\ Ran f = x2 /\
  forall u v, u ∈ x1 /\ v ∈ x1 -> <|u,v|> ∈ r1 <-> <|Value f u , Value f v|> ∈ r2.

Definition Sim W1 W2 := exists Z, sim Z W1 W2.


Definition Fld R :=
  Dom R ∪ (Ran R).

  
Definition TOR R :=
  Rel R /\ Tot R (Fld R).

  
Definition WOR R :=
  Rel R /\ We R (Fld R).

Definition E :=
    {| fun i => exists x y, M x /\ M y /\ i = <|x,y|> /\ x ∈ y|}.

Definition Trans X :=
  forall x, x ∈ X -> x ⊆ X.

    
Definition Sect R X Z :=
  Z ⊆ X /\ (forall u v, u ∈ X -> v ∈ Z -> <|u,v|> ∈ R -> u ∈ Z).

Definition Seg R X U :=
  {: X | fun x => <|x,U|> ∈ R:}.

Definition Ord X :=
    We E X /\ Trans X.

Definition On :=
  {| Ord |}.  






Theorem we_con {R A} :
We R A -> Con R A.
Proof.
  intro H.
  induction H.
  inversion H.
  apply (conj H1).
  intros x y H3.
  induction H3 as [xA]; induction H3 as [yA xy].
  pose (Pairing x y) as U.
  assert (U ⊆  A).
    intros i Hi.
    apply pairing in Hi.
    induction Hi.      
    by subst i.
    by subst i.
    by exists U.
  assert (U <> ∅).
    intro.
    assert (x ∈ U).
      apply pairing.
      by exists A.
      by apply or_introl.
    rewrite H4 in H5.
    assert (x_ : M x) by (by exists A).
    case ((empty x x_) H5).
  specialize (H0 U (conj H3 H4)).
  induction H0 as [m].
  induction H0 as [mU].
  apply pairing in mU.
  assert (y <> x).
    intro.
    apply xy.
    by symmetry.
  assert (y ∈ U).
    apply pairing.
    by exists A.
    by apply or_intror.
  assert (x ∈ U).
    apply pairing.
    by exists A.
    by apply or_introl.
  induction mU as [mx | my].
  + subst m.
    specialize (H0 y (conj H6 H5)).
    induction H0.
    by apply or_introl.
  + subst m.
    specialize (H0 x (conj H7 xy)).
    induction H0.
    by apply or_intror.
  + by exists U.
Qed.

Theorem we_tr {R A} : 
  We R A -> Tr R A.
Proof.
  intro H.
  inversion H.
  inversion H0.
  apply (conj H2).
  intros x y z H4.
  induction H4 as [xA]; induction H4 as [yA]; induction H4 as [zA].
  induction H4 as [xy yz].
  pose ({: A | fun i => i = x \/ i = y \/ i = z:}) as U.
  assert (xU : x ∈ U).
    apply separation.
    apply (conj xA).
    by apply or_introl.
 assert (yU : y ∈ U).
    apply separation.
    apply (conj yA).
    apply or_intror.
    by apply or_introl.
  assert (zU : z∈ U).
    apply separation.
    apply (conj zA).    
    apply or_intror.
    by apply or_intror. 
  assert (forall a b ,a ∈ A -> b ∈ A -> <|a,b|> ∈ R -> a <> b).
    intros a b aA bA abR ab.
    subst b.
    case ((H3 a aA) abR).
  specialize (H4 x y xA yA xy) as x_y.
  specialize (H4 y z yA zA yz) as y_z.
  clear H4.
  assert (U ⊆ A).
    intros i Hi.
    apply separation in Hi.
    apply Hi. 
  assert (U <> ∅).
    intro.
    rewrite H5 in xU.
    assert (x_ : M x) by (by exists ∅).
    case ((empty x x_) xU).
  specialize (H1 U (conj H4 H5)).
  induction H1 as [m]; induction H1 as [mU].
  apply separation in mU.
  induction mU as [mA].
  induction H6 as [mx|H6].
  + subst m.    
    assert (z <> x).
      intro.
      subst z.
      specialize (H1 y (conj yU y_z)).
      induction H1.
      case (H6 yz).
    specialize (H1 z (conj zU H6)).
    apply H1. 
  + induction H6 as [my | mz].
    - subst m.
      specialize (H1 x (conj xU x_y)).
      induction H1.
      case (H6 xy).
    - subst m.
      specialize (H1 y (conj yU y_z)).
      induction H1.
      case (H6 yz).
Qed.

Theorem we_tot {R A} : 
  We R A -> Tot R A.
Proof.
  intro.
  split.
  + apply (we_tr H).
  + split.
    apply H.
    apply (we_con H).
Qed.

Theorem sub_trans {X Y Z} :
    X ⊆ Y -> Y ⊆ Z -> X ⊆ Z.
Proof.
  intros XY YZ i Xi.
  apply (YZ i (XY i Xi)).
Qed.  


Theorem we_sub {R X Y} :
  We R X -> Y ⊆ X -> We R Y.
Proof.
  intros H YX.
  inversion H.
  inversion H0.
  split.
  + apply (conj H2).
    intros x xY.
    specialize ( YX x xY).
    apply (H3 x YX).
  + intros Z HZ.
    induction HZ as [ZY Z0] .
    specialize (sub_trans ZY YX) as ZX.
    induction (H1 Z (conj ZX Z0)) as [m].
    induction H4 as [mZ].
    by exists m.
Qed.    






Theorem inverse_sim f X Y :
    sim f X Y -> sim (Inverse f) Y X.
Proof.
  intro.
  induction H as [x1]; induction H as [x2].
  induction H as [r1]; induction H as [r2].
  induction H as [x1_]; induction H as [x2_].
  induction H as [r1_]; induction H as [r2_].
  induction H as [rel_r1]; induction H as [rel_r2].
  induction H as [X_rx]; induction H as [Y_rx].
  induction H as [rel_f]; induction H as [un_f].
  induction H as [domf]; induction H as [ranf].
  exists x2; exists x1; exists r2; exists r1.
  apply (conj x2_).
  apply (conj x1_).
  apply (conj r2_).
  apply (conj r1_).
  apply (conj rel_r2).
  apply (conj rel_r1).
  apply (conj Y_rx).
  apply (conj X_rx).
  split.
    intros Z ZH.
    apply inverse in ZH.  
    induction ZH as [x]. induction H0 as [y].
    induction H0 as [x_]; induction H0 as [y_].
    induction H0 as [Z_xy yx_f].
    apply product.
    exists x; exists y.
    by repeat rewrite universe.
  split.
    induction un_f.
    rewrite <- (inverse_inverse rel_f) in H0.
    apply (conj H1 H0).
  split.
    by rewrite dom_inverse.
  split.
    by rewrite ran_inverse.
  intros u2 v2 Huv.
  induction Huv as [ux2 vx2].
  assert (u2_ : M u2) by (by exists x2).
  assert (v2_ : M v2) by (by exists x2).
  rewrite <- ranf in ux2.
  apply ran in ux2.
  induction ux2 as [u]; induction H0 as [u_ uu_f].
  rewrite <- ranf in vx2.
  apply ran in vx2.
  induction vx2 as [v]; induction H0 as [v_ vv_f].
  assert (u_dom : u ∈ Dom f).
    apply dom.
    done.
    by exists u2.
  assert (v_dom : v ∈ Dom f).
    apply dom.    
    done.
    by exists v2.
  induction un_f as [un_f un1_f].
  apply (eq_value f u u2 u_ u2_ un_f u_dom) in uu_f.
  apply (eq_value f v v2 v_ v2_ un_f v_dom) in vv_f.
  subst u2 v2.
  rewrite <- (value_value f u (conj un_f un1_f) u_dom).
  rewrite <- (value_value f v (conj un_f un1_f) v_dom).
  rewrite domf in u_dom.
  rewrite domf in v_dom.
  specialize (H u v (conj u_dom v_dom)).
  by rewrite H.
  done.
  done.
Qed.

Theorem sim_set {f X Y} :
    sim f X Y -> M f /\ M X /\ M Y.
Proof.
  intro H.
  induction H as [x1]; induction H as [x2].
  induction H as [r1]; induction H as [r2].
  induction H as [x1_]; induction H as [x2_].
  induction H as [r1_]; induction H as [r2_].
  induction H as [rel_r1]; induction H as [rel_r2].
  induction H as [X_rx]; induction H as [Y_rx].
  induction H as [rel_f]; induction H as [un_f].
  induction H as [domf]; induction H as [ranf].
  split.
  + assert (f ⊆ (x1 × x2)).
    intros i Hi.
    apply product.
    specialize (rel_f i Hi).
    apply product in rel_f.
    induction rel_f as [x]; induction H0 as [y].
    induction H0 as [x_]; induction H0 as [y_].
    induction H0 as [i_xy _].
    exists x; exists y.
    apply (conj x_).
    apply (conj y_).
    apply (conj i_xy).
    subst i.
    split.
    - rewrite <- domf.
      apply dom.
      done.      
      by exists y.
    - rewrite <- ranf.
      apply ran.
      done.
      by exists x.
    - refine (sub_set f (x1 × x2) _ H0).
      by apply product_set.
  + subst X Y.
    split.
    by apply op_set.
    by apply op_set.
Qed.    

Theorem sim_comm X Y :
  Sim X Y -> Sim Y X.
Proof.
  intro.  
  induction H as [f].
  exists (Inverse f).
  by apply inverse_sim.
Qed.


Theorem sim_trans X Y U :
  Sim X Y -> Sim Y U -> Sim X U.
Proof.
  intros XY YU.

  induction XY as [f XY].
  induction XY as [x1]; induction H as [x2].
  induction H as [r1]; induction H as [r2].
  induction H as [x1_]; induction H as [x2_].
  induction H as [r1_]; induction H as [r2_].
  induction H as [rel_r1]; induction H as [rel_r2].
  induction H as [X_rx]; induction H as [Y_rx].
  induction H as [rel_f]; induction H as [un1_f].
  induction H as [domf]; induction H as [ranf fXY].

  induction YU as [g YU].
  induction YU as [y1]; induction H as [y2].
  induction H as [s1]; induction H as [s2].
  induction H as [y1_]; induction H as [y2_].
  induction H as [s1_]; induction H as [s2_].
  induction H as [rel_s1]; induction H as [rel_s2].
  induction H as [Y_sy]; induction H as [U_sy].
  induction H as [rel_g]; induction H as [un1_g].
  induction H as [domg]; induction H as [rang gYU].

  exists (g ○ f).
  exists x1; exists y2.
  exists r1; exists s2.
  apply (conj x1_); apply (conj y2_).
  apply (conj r1_); apply (conj s2_).
  apply (conj rel_r1); apply (conj rel_s2).
  apply (conj X_rx); apply (conj U_sy).
  split.
    intros i H.
    apply composition in H.
    induction H as [x]; induction H as [y]; induction H as [z].
    induction H as [x_]; induction H as [y_]; induction H as [z_].
    induction H as [Hi].
    apply product.
    exists x; exists z.
    by repeat rewrite universe.
  split.
    induction un1_f.
    induction un1_g.
    split.
    by apply un_composition.
    rewrite inverse_composition.
    by apply un_composition.
  rewrite Y_sy in Y_rx.
  apply (OP_eq s1 y1 r2 x2 s1_ y1_ r2_ x2_) in Y_rx.
  induction Y_rx.
  subst s1.
  rewrite H0 in domg.
  rewrite <- domg in ranf.

  split.
    rewrite <- domf.
    apply equal => x.
    split => [H | H].
      (* -> *)
      assert (x_ : M x) by (by exists (Dom (g ○ f))).
      apply dom in H.
      induction H as [z]; induction H as [z_].
      apply in_composition in H.
      induction H as [y]; induction H as [y_].
      induction H as [xy_f _].
      apply dom.
      done.
      by exists y.
      (* <- *)
      done.
      done.
      done.
      assert (x_ : M x) by (by exists (Dom f)).
      apply dom in H.
      induction H as [y]; induction H as [y_ xy_f].
      apply dom.
      done.
      assert (y ∈ Dom g).
        rewrite <- ranf.
        apply ran.
        done.
        by exists x.
      apply dom in H.
      induction H as [z]; induction H as [z_ yz_g].
      exists z.
      apply (conj z_).
      apply in_composition.
      done.
      done.
      by exists y.
      done.
      done.
  split.
    rewrite <- rang.
    apply equal => z.
    split => [H | H].
      (* -> *)
      assert (z_ : M z) by (by exists (Ran (g ○ f))).
      apply ran in H.
      induction H as [x]; induction H as [x_ H].
      apply in_composition in H.
      induction H as [y]; induction H as [y_].
      induction H as [xy_f yz_g].
      apply  ran.
      done.
      by exists y.
      done.
      done.
      done.
      (* <- *)
      assert (z_ : M z) by (by exists (Ran g)).
      apply ran in H.
      induction H as [y]; induction H as [y_ yz_g].
      apply ran.
      done.
      assert (y ∈ Ran f).
        rewrite ranf.
        apply dom.
        done.
        by exists z.
      apply ran in H.
      induction H as [x]; induction H as [x_ xy_f].
      exists x.
      apply (conj x_).
      apply in_composition.
      done.
      done.
      by exists y.
      done.
      done.
  intros u v Huv.
  subst y1.
  rewrite (fXY u v Huv).
  assert (H : forall x, x ∈ x1 -> Value f x ∈ x2).
    intros x xx.
    rewrite <- domf in xx.
    induction un1_f as [un_f _].
    specialize (value f x un_f xx) as H.
    induction H.
    rewrite <- domg.
    rewrite <- ranf.
    apply ran.
    done.
    assert (x_ : M x) by (by exists (Dom f)).
    by exists x.
  assert (Value f u ∈ x2 /\ Value f v ∈ x2).
    induction Huv.
    split.
    by apply H.
    by apply H.
  rewrite (gYU (Value f u) (Value f v) H0).
  induction un1_f as [un_f _].
  induction un1_g as [un_g _].
  specialize (un_composition un_f un_g) as un_gf.
  assert (forall x, x ∈ x1 -> Value g (Value f x) = Value (g ○ f) x).
    intros x xx.
    assert (x_ : M x) by (by exists x1).
    assert (vv_gf_ : M (Value g (Value f x))).
      apply value_set.
      done.
      rewrite <- ranf.
      rewrite <- domf in xx.
      specialize (value f x un_f xx)  as H1.
      induction H1.
      apply ran.
      done.
      by exists x.
    assert (x ∈ (Dom (g ○ f))).
      apply dom.
      done.
      exists (Value g (Value f x)).
      apply (conj vv_gf_).
      apply in_composition.
      done.
      done.
      exists (Value f x).
      split.
      apply value_set.
      done.
      by rewrite domf.
      split.
      apply value.
      done.
      by rewrite domf.
      apply  value.
      done.
      rewrite <- domf in xx.
      specialize (value f x un_f xx) as H1.
      induction H1.
      rewrite <- ranf.
      apply ran.
      done.
      by exists x.
    specialize (eq_value (g ○ f) x (Value g (Value f x)) x_ vv_gf_ un_gf H1) as H2.
    apply H2.
    apply in_composition.
    done.
    done.
    exists (Value f x).
    rewrite <- domf in xx.
    specialize (value f x un_f xx) as H3.
    induction H3.
    split.
    done.
    split.
    done.
    apply value.
    done.
    rewrite <- ranf.
    apply ran.
    done.
    by exists x.
  induction Huv.    
  rewrite (H1 u H2).
  rewrite (H1 v H3).
  done.
Qed.



  



Theorem sim_tor X Y :
  Sim (<|X, Fld X|>) (<|Y, Fld Y|>) -> TOR X <-> TOR Y.
Proof.
  intro H.
  induction H as [f].
  induction H as [x1]; induction H as [x2].
  induction H as [r1]; induction H as [r2].
  induction H as [x1_]; induction H as [x2_].
  induction H as [r1_]; induction H as [r2_].
  induction H as [rel_r1]; induction H as [rel_r2].
  induction H as [X_rx]; induction H as [Y_rx].
  induction H as [rel_f]; induction H as [un1_f].
  induction H as [domf]; induction H as [ranf fXY].  
  split => [H | H].
  + induction H as [rel_X].
    induction H.
    induction H0.
    induction H as [_ Tr_X].
    induction H0 as [_ Irr_X].
    induction H1 as [_ Con_X].
    unfold Rel in rel_X.
    assert (X_ : M X).
      apply (sub_set X V²).
      apply product_set.

 admit.
Admitted.

Theorem sim_wor X Y :
  Sim (<|X, Fld X|>) (<|Y, Fld Y|>) -> WOR X <-> WOR Y.
Admitted.



Goal forall X, Trans X <-> (forall u v, u ∈ v /\ v ∈ X -> u ∈ X).
Proof.
  intro X.
  split => [H | H].
  + intros u v H0.
    induction H0.
    by specialize ((H v H1) u H0).
  + intros v Hv u uv.
    apply (H u v (conj uv Hv)).
Qed.

Theorem union_sub {X} :
    Trans X <-> ⊔ X ⊆ X.
Proof.
  split => [H | H].
  + intros x xX.
    apply union in xX.
    induction xX as [Y HY].
    induction HY as [xY YX].
    by specialize ((H Y YX) x xY).
  + intros Y YX x xY.
    apply H.
    apply union.
    by exists Y.
Qed.

Theorem cap_trans {X Y} :
    Trans X -> Trans Y -> Trans (X ∩ Y).
Proof.
  intros HX HY U UXY i iU.
  apply cap in UXY.
  induction UXY.
  apply cap.
  split.
  + by specialize ((HX U H) i iU).
  + by specialize ((HY U H0) i iU).
Qed.

Theorem cup_trans {X Y}:
    Trans X -> Trans Y -> Trans (X ∪ Y).
Proof.
  intros HX HY U UXY i iU.
  apply cup in UXY.
  apply cup.
  induction UXY.
  + apply or_introl.
    by specialize ((HX U H) i iU).
  + apply or_intror.
    by specialize ((HY U H) i iU).
Qed.

Theorem seg_cap {X u} (u_ : M u) :
    Seg E X u = X ∩ u.
Proof.
  apply equal => i.
  split => [H | H].
  + assert (i_ : M i) by (by exists (Seg E X u)).
    move : H.
    rewrite classify.
    intro.
    induction H as [iX iuE].
    move : iuE.
    rewrite classify.
    intro.
    induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [iuxy xy].
    apply (OP_eq i u x y i_ u_ x_ y_)in iuxy .
    induction iuxy; subst x y.
    by apply cap.
    by apply op_set.
    done. 
  + apply cap in H.
    induction H as [iX iu].
    assert (i_ : M i) by (by exists u).
    apply classify.
    done.
    apply (conj iX).
    apply classify.
    by apply op_set.
    by exists i; exists u.
Qed.


Theorem segE_set {X u} (u_ : M u):
    M (Seg E X u).
Proof.
  apply (sub_set _ u).
  done.
  rewrite seg_cap.
  done.
  intros i Hi.
  apply cap in Hi.
  apply Hi.
Qed.

Theorem trans_seg {X} :
  Trans X <-> forall u, M u -> u ∈ X -> Seg E X u = u.
Proof.
  split => [H | H].
  + intros u u_ uX.
    apply equal => i.
    rewrite separation.
    split => [H0 | H0].
    - induction H0.
      move : H1.
      assert (i_ : M i) by (by exists X).
      rewrite classify.
      intro.
      induction H1 as [x]; induction H1 as [y].
      induction H1 as [x_]; induction H1 as [y_].
      induction H1 as [iuxy xy].     
      apply OP_eq in iuxy.
      by induction iuxy; subst x y.
      done.
      done.
      done.
      done.
      by apply op_set.
    - assert (i_ : M i) by (by exists u).
      unfold Trans in H.
      specialize ((H u uX) i H0).
      apply (conj H).
      apply classify.
      by apply op_set.
      by exists i; exists u.      
  + intros x xX i ix.
    assert (x_ : M x) by (by exists X).
    specialize (H x x_ xX).
    rewrite <- H in ix.
    apply separation in ix.
    apply ix.
Qed.    

Theorem in_E {x y} {x_ : M x} {y_ : M y}:
  <|x,y|> ∈ E <-> x ∈ y.
Proof.
  rewrite classify.
  split => [H | H].
  + induction H as [a]; induction H as [b].
    induction H as [a_]; induction H as [b_] .
    induction H as [abxy ab].
    apply OP_eq in abxy.
    by induction abxy; subst a b.
    done. done. done. done.
  + by exists x; exists y.
  + by apply op_set.
Qed.    

Theorem segE_cap {X Y} {Y_ : M Y}:
    Seg E X Y = X ∩ Y.
Proof.
  apply equal => i.
  split => [H | H].
  + assert (i_ : M i) by (by exists (Seg E X Y)).
    move : H.
    rewrite separation.
    rewrite in_E.
    rewrite cap.
    done. done. done.
  + assert (i_ : M i) by (by exists (X ∩ Y)).
    apply  cap in H.
    apply separation.
    rewrite in_E.
    done. done. done.
Qed.    


Theorem we_sect_seg {X Z} :
  We E X -> Sect E X Z -> Z <> X -> exists u, u ∈ X /\ Z = Seg E X u.
Proof.
  intros.
  induction H.
  induction H0.
  pose (X  // Z) as Y.
  assert (Y ⊆ X).
    intros i iY.
    apply diff in iY.
    apply iY.
  assert (Y <> ∅).
    intro Y0.
    apply H1.
    apply equal => i.
    split => [iZ | iX].
      (* iZ *)
      apply (H0 i iZ).
      (* iX *)        
      assert (i_ : M i) by (by exists X).
      specialize (empty i i_) as i0.
      rewrite <- Y0 in i0.
      move : i0.
      apply contrapositive.
      intro.
      apply DoubleNegative.
      apply diff.
      done.
  specialize (H2 Y (conj H4 H5)) as H2_.
  induction H2_ as [m]. (* min of X // Z*)
  induction H6 as [mY].
  apply diff in mY.
  induction mY.
  pose (Y // (Single m))
  (*  途中    *)

  




Theorem on_ord {x} {x_ : M x} :
    x ∈ On <-> Ord x.
Proof.
  by rewrite classify.
Qed.


  Theorem empty_on : 
    ∅ ∈ On.
  Proof.
    specialize empty_set as em_.
    rewrite classify.
    split.
    + unfold We.
      split.
      unfold Irr.
      split.
      intros p pE.
      assert (p_ : M p) by (by exists E).
      move : pE.
      repeat rewrite classify.
      intro.
      induction H as [x]; induction H as [y].
      induction H as [x_]; induction H as [y_].
      induction H as [p_xy xy].
      exists x; exists y.
      by repeat rewrite universe.
      auto.
      auto.
      intros x H.
      assert (x_ : M x) by (by exists ∅).
      case ((empty x x_) H).
      intros Y H.    
      induction H.
      assert (Y = ∅).
        apply equal => i.
        split => [H1 | H1].
        specialize (H i H1).
        assert (i_ : M i) by (by exists Y).
        case ((empty i i_) H).
        assert (i_ : M i) by (by exists ∅).
        case ((empty i i_) H1).
      case (H0 H1).
    + intros i H.
      assert (i_ : M i) by (by exists ∅).
      case ((empty i i_) H).
    + done.
  Qed.

Theorem ord_irr {X} :
  Ord X  -> ~ X ∈ X.
Proof.
  intros H XX.
  assert (X_ : M X) by (by exists X).
  induction H.
  induction H.
  induction H.
  specialize (H2 X XX).
  apply H2.
  apply classify.  
  by apply op_set.
  by exists X; exists X.
Qed.




Theorem ord_in_irr {X} :
  Ord X -> forall x, x ∈ X -> ~ x ∈ x.
Proof.
  intros H x xX xx.
  assert (x_ : M x) by (by exists X).
  induction H.
  induction H.
  induction H.
  specialize (H2 x xX).
  apply H2.
  by rewrite in_E.
Qed.

Theorem sub_refl {X} :
  X ⊆ X.
Proof.
  done.
Qed.

Theorem not_empty {X} :
  X <> ∅ <-> exists x, x ∈ X.
Proof.
  split.
  + apply contrapositive.
    rewrite <- allnot_notexists.
    intro.
    apply DoubleNegative. 
    apply equal => i.
    split => [iX | i0].
    - case ((H i) iX).
    - assert (i_ : M i) by (by exists ∅ ).
      case ((empty i i_) i0).
  + intro H.
    induction H as [x].
    intro X0.
    assert (x_ : M x) by (by exists X).
    rewrite X0 in H.
    case ((empty x x_) H).
Qed.    




Theorem ord_sub_trans_in {X Y} :
  Ord X -> Y ⊂ X -> Trans Y -> Y ∈ X.
Proof.
  intros ordX YX transY.
  inversion  ordX.
  induction  H.
  induction H.
  induction YX.
  case (ExcludedMiddle (Y = ∅)) as [Y0 | notY0].
  + subst Y.
    assert (X <> ∅) .
      intro X0.
      symmetry in X0.
      apply equal in X0.
      case (H4 X0).
    specialize (H1 X (conj sub_refl H5)).
    induction H1 as [m].
    induction H1 as [mX].
    case (ExcludedMiddle (m = ∅)) as [m0 | notm0].
    - by rewrite m0 in mX.
    - assert (m_ : M m) by (by exists X).
      apply not_empty in notm0.
      induction notm0.
      assert (x_ : M x) by (by exists m).
      assert (x <> m).
        intro xm.
        subst x.
        apply ((H2 m mX)).
        rewrite in_E.
        done. done. done.
      specialize ((H0 m mX) x H6).
      specialize (H1 x (conj H0 H7)).
      induction H1.
      move : H8.
      rewrite in_E.
      intro.
      case (H8 H6).
      done. done.
  + pose (X // Y ) as Z.
    assert (Z ⊆ X).
      intros i iZ.
      apply diff in iZ.
      apply iZ.
    assert (Z <> ∅).
      intro Z0.
      apply H4.
      intro i.
      split => [iY | iX].
        (* iY *)
        apply (H3 i iY).
        (* iX *)        
        assert (i_ : M i) by (by exists X).
        specialize (empty i i_) as i0.
        rewrite <- Z0 in i0.
        move : i0.
        apply contrapositive.
        intro.
        apply DoubleNegative.
        apply diff.
        done.
    specialize (H1 Z (conj H5 H6)) as H7.
    induction H7 as [n].
    induction H7 as [nZ].
    apply diff in nZ.
    induction nZ.

    specialize (H1 Y (conj H3 notY0)).
    induction H1 as [m].
    induction H1 as [mY].

    apply not_empty in notY0.
    induction notY0 as [y] .

    case (ExcludedMiddle (Y ∈ Z)) as [YZ | notYZ] .
    - apply (H5 Y YZ).
    - 






    
      


















  

      
    




    







  
  







    















    


  



  


  











  
    
      