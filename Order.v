Require Export Maps.

Definition Max R X x :=
  x ∈ X /\ ~ exists y, y ∈ X /\ <|x,y|> ∈ R.

Definition Min R X x :=
  x ∈ X /\ ~ exists y, y ∈ X /\ <|y,x|> ∈ R.

Definition WellFounded R A :=
  forall X, X <> ∅ -> X ⊆ A -> exists x, Min R X x.

Definition WellOrderd R A :=
    Total R A /\ WellFounded R A.

    
Theorem sub_wellorderd R A :
  WellOrderd R A -> forall X, X ⊆ A -> WellOrderd R X.
Proof.
  intros H X XA.
  unfold WellOrderd.
  unfold Total.
  unfold Trans.
  unfold NonRefl.
  unfold Tri.
  unfold WellFounded.
  induction H.
  induction H.
  induction H.
  induction H1.
  induction H1 as [_ H1].
  induction H3 as [_ H3].  
  unfold WellFounded in H0.
  split.
  split.
  + apply (conj H).
    intros x y z xX yX zX xyR yzR.
    apply (H2 x y z (XA x xX) (XA y yX) (XA z zX) xyR yzR).
  + split.
    - apply (conj H).
      intros x xX.
      apply (H1 x (XA x xX)).
    - apply (conj H).
      intros x y xX yX.
      apply (H3 x y (XA x xX) (XA y yX)).
  + intros Y Y0 YX.
    apply H0.
    apply Y0.
    intros i iY.
    apply XA.
    apply YX.
    done.
Qed.

Definition TransSet X :=
    forall x, x ∈ X -> x ⊆ X.

Definition InRel :=
    {|fun p => exists x y, M x /\ M y /\ p = <|x,y|> /\ x ∈ y|}.

Theorem inrel x y (x_ : M x) (y_ : M y):
   <|x,y|> ∈ InRel <-> x ∈ y.
Proof.
  rewrite classify.
  split => [H | H].
  + induction H as [x0]; induction H as [y0].
    induction H as [x0_]; induction H as [y0_].
    induction H.
    apply (OP_eq x y x0 y0 x_ y_ x0_ y0_) in H.
    by induction H; subst x0 y0.
  + by exists x; exists y.
  + by apply op_set.
Qed.

Definition Ord X :=
    TransSet X /\ WellOrderd InRel X.

Definition ON :=
  {|Ord|}.

Theorem on X (X_ : M X):
    X ∈ ON <-> Ord X.
Proof.
  split => [H | H].
  + move : H.
    rewrite classify.
    auto.
    done.
  + inversion H.
    by apply classify.
Qed.    

Theorem ontrans X:
    X ∈ ON -> X ⊆ ON.
Proof.
  intros XON x xX.
  assert (X_ : M X) by (by exists ON).
  assert (x_ : M x) by (by exists X).
  apply (on X X_) in XON.
  induction XON.
  inversion H0.
  induction H1.
  induction H1.
  apply on.
  done.
  split.
  + intros y yx z zy.
    specialize (H x xX y yx) as yX.
    specialize (H y yX z zy) as zX.
    rewrite <- inrel.
    apply inrel in zy.
    apply inrel in yx.
    apply (H4 z y x zX yX xX zy yx).    
    by exists X.
    by exists X.
    by exists X.
    by exists X.
    by exists X.
    by exists X. 
  + apply (sub_wellorderd InRel X).
    done.
    apply (H x xX).
Qed.

Theorem cap_on a b :
    a ∈ ON -> b ∈ ON -> a ∩ b ∈ ON.
Proof.
  intros aON bON.
  assert (a_ : M a) by (by exists ON).
  assert (b_ : M b) by (by exists ON).
  assert (ab_ : M (a ∩ b)) by (by apply cap_set).  
  rewrite (on (a ∩ b) ab_).  
  apply (on a a_) in aON.
  apply (on b b_) in bON.
  induction aON.
  induction bON.
  split.
  + clear H0 H2.
    intros x xab i ix.
    apply cap.
    apply cap in xab.
    induction xab as [xa xb].
    specialize (H x xa i ix).
    specialize (H1 x xb i ix).
    done.
  + apply (sub_wellorderd InRel a H0).
    intros i iab.
    apply cap in iab.
    by induction iab.
Qed.

Lemma not_empty X :
    X <> ∅ <-> exists x, x ∈ X.
Proof.
  split => [| H].
  + apply contrapositive.
    rewrite <- allnot_notexists.
    intro H.
    apply DoubleNegative.
    apply equal => i.
    specialize (H i).
    split => [iX | i0].
    - case (H iX).
    - assert (i_ : M i) by (by exists ∅).
      case ((empty i i_) i0).
  + induction H as [x xX].
    intro X0.
    assert (x_ : M x) by (by exists X).
    rewrite X0 in xX.
    apply ((empty x x_) xX).
Qed.  

Lemma diff_sub x y :
    x // y = ∅ <-> x ⊆ y.
Proof.
  rewrite equal.
  split => [H i ix |H i].
  + specialize (H i).
    induction H.
    apply contrapositive in H.
    move : H.
    rewrite diff.
    rewrite DeMorgan_notand.
    intro H.
    induction H.
    - case (H ix).
    - by rewrite <- DoubleNegative.
    - apply empty.
      by exists x.
  + split => [ixy | i0].
    - apply diff in ixy.
      induction ixy.
      case (H1 (H i H0)).
    - assert (i_ : M i) by (by exists ∅).
      case ((empty i i_) i0).
Qed.

Theorem on_set {x} :
  x ∈ ON -> M x.
Proof.
  intro H.
  by exists ON.
Qed.
    




Theorem sub_on a b :
  a ∈ ON -> b ∈ ON -> a ⊆ b <-> a ∈ b \/ a = b.
Proof.
  intros aON bON.
  specialize (on_set aON) as a_.
  specialize (on_set bON) as b_.
  apply (on a a_) in aON.
  apply (on b b_) in bON.
  inversion aON.
  induction bON.  
  split => [H3 | H3].
  + case (ExcludedMiddle (a = b)) as [ab | notab].
    - by apply or_intror.
    - apply or_introl.
      assert (~ b ⊆ a).
      * intro ba.
        apply notab.
        apply equal => i.
        split => [ia | ib].
          by specialize (H3 i ia).
          by specialize (ba i ib).      
      * induction  (diff_sub b a) as [H5 _].
        apply contrapositive in H5.
        assert (b // a ⊆ b).
          intros i iba.
          apply diff in iba.
          apply iba.
        induction H2.
        specialize (H7 (b//a) H5 H6).
        induction H7 as [x].
        induction H7.
        move : H8.
        rewrite <- allnot_notexists.      
        intro H8.
        apply diff in H7.
        induction H7 as [xb notxa].
        assert (x_ : M x) by (by exists b).                
        specialize (H1 x xb).
        assert (x //  a = ∅).
          apply equal => i.
          split => [ixa | i0].
            apply diff in ixa.
            induction ixa.
            specialize (H8 i).
            apply DeMorgan_notand in H8.
            induction H8.
            move : H8.
            rewrite diff.
            rewrite DeMorgan_notand.
            intro H8.
            induction H8.
            case (H8 (H1 i H7)).
            case (H8 H9).
            apply inrel in H7.
            case (H8 H7).
            by exists x.
            by exists b.
            assert (i_ : M i) by (by exists ∅).
            case ((empty i i_) i0).
        apply diff_sub in H7 as H10.
        case (ExcludedMiddle (a ⊆ x)) as [ax | notax].
          assert (a = x).
            apply equal => i.
            split => [ia |ix].
              by specialize (ax i ia).
              by specialize (H10 i ix).
            by subst a.

            assert (a // x <> ∅).
              intro.
              apply diff_sub in H9.
              case (notax H9).
            apply not_empty in H9.
            induction H9 as [y].           
            apply diff in H9.
            induction H9.
            assert (y_ : M y) by (by exists a).
            specialize (H y H9) as H12.
            induction H2.
            induction H13.
            induction H14.
            specialize (H15 x y xb (H3 y H9)).
            move : H15.
            repeat rewrite inrel.
            intro.
            induction H15 as [xy | H15].
              specialize (H y H9).
              specialize (H x xy).
              case (notxa H).
              induction H15 as [yx | xy].
                case (H11 yx).
                subst y.
                case (notxa H9).
            done.
            done.
            done.
            done.
            done.
  + intros i ia.
    induction H3 as [ab | ab].
    - by specialize (H1 a ab i ia).
    - by subst b.
Qed. 



Theorem on_trans a b c (a_ : Ord a) (b_ : Ord b) (c_ : Ord c) :
  a ∈ b -> b ∈ c -> a ∈ c.
Proof.
  induction c_.
  intros ab bc.
  by specialize (H b bc a ab).
Qed.

Theorem on_notrefl a (a_ : Ord a) :
  ~ a ∈ a.
Proof.
  intro aa.
  induction a_.
  induction H0.
  induction H0.
  induction H2.
  induction H2.
  specialize (H4 a aa).
  apply inrel in aa.
  apply (H4 aa).
  by exists a.
  by exists a.
Qed.

Theorem on_tri a b (a_ : a ∈ ON) (b_ : b ∈ ON) : 
  a ∈ b \/ b ∈ a \/ a = b.
Proof.
  pose (a ∩ b) as u.
  specialize (cap_on a b a_ b_) as u_.
  assert (u ⊆  a).
  intros i iu.  
  apply cap in iu.
  apply iu.
  assert (u ⊆ b).    
  intros i iu.
  apply cap in iu.
  apply iu.
  apply (sub_on u a u_ a_) in H.
  apply (sub_on u b u_ b_) in H0.
  induction H as [ua | ua].
  - induction H0 as [ub | ub].  
    + apply on in u_.
      assert (u ∈ u).
        by apply cap.
      case (on_notrefl u u_ H).
      apply cap_set.
      by exists ON.
    + rewrite ub in ua.
      apply or_intror.
      by apply or_introl.
  - induction H0 as [ub | ub].
    + rewrite ua in ub. 
      by apply or_introl.
    + rewrite ua in ub.
      apply or_intror.
      by apply or_intror.
Qed.

Theorem on_wellfounded :
  forall X, X <> ∅ -> X ⊆ ON -> exists x, Min InRel X x.
Proof.
  intros X H X_.
  apply not_empty in H.
  induction H as [x].
  specialize (X_ x H).
  assert (x_ : M x) by (by exists X).
  apply (on x x_) in X_.
  induction X_.
  induction H1.
  induction H1.
  induction H3.
  induction H1.
  induction H3 as [_ H3].
  induction H4 as [_ H4].
  case (ExcludedMiddle (Min InRel X x)) as [H6 | H6].
  + by exists x.
  + apply DeMorgan_notand in H6.
    induction H6 as [F | H6].
    - case (F H).
    - move : H6.
      rewrite DoubleNegative.
      intro.
      induction H6 as [y].
      induction H6 as [yX yx].
      move : yx.
      rewrite inrel.
      intro yx.
      assert (x ∩ X <> ∅).
        rewrite not_empty.
        exists y.
        by apply cap.
      assert (x ∩ X ⊆ x).
        intros i ixX.
        apply cap in ixX.
        apply ixX.
      specialize (H2 (x ∩ X) H6 H7).
      induction H2 as [z].
      induction H2.
      apply cap in H2.
      induction H2.
      exists z.
      apply (conj H9).
      intro.
      apply H8.
      induction H10 as [a]; induction H10 as [aX az].
      move : az.
      rewrite inrel.
      intro az.
      specialize (H0 z H2).
      specialize (H0 a az).    
      exists a.
      split.
      * by apply cap.
      * rewrite inrel.
        apply az.
        by exists X.
        by exists x.
      * by exists X.
      * by exists X.
      * by exists X.
      * by exists X.
Qed.



Theorem cap_min a b (aON : a ∈ ON) (bON : b ∈ ON) :
  a ∈ b -> a = a ∩ b.
Proof.  
  intro ab.
  assert (b_ : M b) by (by exists ON).
  apply (on b b_) in bON.
  apply equal => i.
  split => [ia | iab].
  + apply cap.
    apply (conj ia).
    induction bON.
    specialize (H a ab).
    by specialize (H i ia).
  + apply cap in iab.
    apply iab.
Qed.

Theorem cup_max a b (aON : a ∈ ON) (bON : b ∈ ON) :
  a ∈ b -> b = a ∪ b.
Proof.
  intro ab.
  apply equal => i.
  split => [ib | iab].
  + apply cup.
    by apply or_intror.
  + apply cup in iab.
    induction iab as [ia | ib].
    - apply on in bON.
      induction bON.
      by specialize (H a ab i ia).
      by exists ON.
    - done.
Qed.



Theorem cup_on a b (aON : a ∈ ON) (bON : b ∈ ON) :
  a ∪ b ∈ ON.
Proof.  
  specialize (on_tri a b aON bON) as H.
  induction H as [ab | H].
  + specialize (cup_max a b aON bON ab) as H.
    by rewrite <- H.
  + induction H as [ba | ab].
    - specialize (cup_max b a bON aON ba) as H.
      rewrite cup_comm.
      by rewrite <- H.
    - rewrite ab.
      assert (b ∪ b = b).
        apply equal.
        intro i.
        rewrite cup.
        split => [H | H].
        * by induction H.
        * by apply or_introl.
        * by rewrite H.
Qed.      

Theorem union_on X (XON : X ∈ ON) :
  X <> ∅ -> ⊔ X ∈ ON.
Proof.
  intro X0.
  apply not_empty in X0.
  induction X0 as [a aX].
  assert (X_ : M X) by (by exists ON).
  assert (H0 : forall x, x ∈ ⊔ X -> x ∈ ON).
    intros x H.
    apply union in H.
    induction H as [Y]; induction H as [xY YX].
    specialize (ontrans X XON) as H0.
    specialize (H0 Y YX).
    specialize (ontrans Y H0) as H1 .
    by specialize (H1 x xY).
  apply on.
  by apply union_set.
  specialize (ontrans X XON) as X_ON.
  apply (on X X_) in XON.
  induction XON as [tr we].
  split.
  + intros x H i ix.
    apply union in H.
    induction H as [Y]; induction H as [xY YX].
    apply union.
    exists Y.
    split.
    - specialize ((X_ON Y YX)).
      assert (Y_ : M Y) by (by exists ON).
      apply (on Y Y_) in X_ON.
      induction X_ON.
      by specialize ((H x xY) i ix).
    - done.
  + induction we.
    induction H.
    induction H2.
    induction H as [R tra].
    induction H2 as [_ nonrefl].
    induction H3 as [_ tri].
    split.
    - split.
      * apply (conj R). 
        intros x y z x_ y_ z_.
        apply (H0 x) in x_.
        apply (H0 y) in y_.
        apply (H0 z) in z_.
        assert (x__ : M x) by (by exists ON).
        assert (y__ : M y) by (by exists ON).
        assert (z__ : M z) by (by exists ON).
        apply (on x x__) in x_.
        apply (on y y__) in y_.
        apply (on z z__) in z_.
        rewrite (inrel x y x__ y__).
        rewrite (inrel y z y__ z__).
        rewrite (inrel x z x__ z__).
        apply (on_trans x y z x_ y_ z_).
      * split.
          (* NonRefl *)
          apply (conj R).
          intros x H.
          specialize (H0 x H).
          assert (x_ : M x) by (by exists ON).
          apply (on x x_) in H0.
          rewrite (inrel x x x_ x_).
          apply (on_notrefl x H0).
          (* tri *)
          apply (conj R).
          intros x y x__ y__.
          apply (H0 x) in x__.
          apply (H0 y) in y__.
          assert (x_ : M x) by (by exists ON).
          assert (y_ : M y) by (by exists ON).       
          rewrite (inrel x y x_ y_).
          rewrite (inrel y x y_ x_).
          apply (on_tri x y x__ y__) .
    - intros x x0 x_X.
        apply (not_empty x ) in x0.
        induction x0 as [i ix].
        specialize (x_X i ix) as H10.
        apply union in H10.
        induction H10 as [Y].
        induction H as [iY YX].
        specialize ((tr Y YX) i iY) as iX.
        assert (x ∩ X ⊆ X).
          intros j H.
          apply cap in H.
          apply H.
        assert (i ∈ x ∩ X).
          by apply cap.
        assert (x ∩ X <> ∅).
          apply not_empty.
          by exists i.        
        specialize (H1 (x ∩ X) H3 H).
        induction H1 as [j].
        induction H1.
        apply cap in H1.
        induction H1.
        exists j.
        apply (conj H1).
        intro.
        apply H4.
        induction H6 as [k].        
        induction H6.
        specialize (x_X k H6).
        apply union in x_X.
        induction x_X as [Z].
        induction H8.
        specialize ((tr Z H9) k H8).
        assert (k ∈ x ∩ X).
          by apply cap.
        by exists k.
Qed.        
        


        
      



    
      
      


    



   