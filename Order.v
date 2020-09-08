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
    M X /\ forall x, x ∈ X -> x ⊆ X.

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

Theorem on X :
    X ∈ ON <-> Ord X.
Proof.
  split => [H | H].
  + assert (X_ : M X) by (by exists ON).
    move : H.
    rewrite classify.
    auto.
    done.
  + inversion H.
    induction H0 as [X_ _].   
    by apply classify.
Qed.    

Theorem on_trnas X:
    X ∈ ON -> X ⊆ ON.
Proof.
  intros XON x xX.
  assert (x_ : M x) by (by exists X).
  apply on in XON.
  induction XON.
  induction H as [X_ H].
  inversion H0.
  induction H1.
  induction H1.
  apply on.
  split.
  + apply (conj x_) .
    intros y yx z zy.
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
  rewrite on.  
  apply on in aON.
  apply on in bON.
  induction aON.
  induction bON.
  split.
  + clear H0 H2.
    induction H as [a_ H].
    induction H1 as [b_ H1].
    split.
    - by apply cap_set.
    - intros x xab i ix.
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


Theorem sub_on a b :
  a ∈ ON -> b ∈ ON -> a ⊆ b <-> a ∈ b \/ a = b.
Proof.
  intros aON bON.
  assert (aon : a ∈ ON) by done .
  assert (a_ : M a) by (by exists ON).
  apply on in aON.
  apply on in bON.
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
        induction H1.
        specialize (H7 x xb).
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
            case (H8 (H7 i H9)).
            case (H8 H10).
            apply inrel in H9.
            case (H8 H9).
            by exists x.
            by exists b.
            assert (i_ : M i) by (by exists ∅).
            case ((empty i i_) i0).
        apply diff_sub in H9 as H10.
        case (ExcludedMiddle (a ⊆ x)) as [ax | notax].
          assert (a = x).
            apply equal => i.
            split => [ia |ix].
              by specialize (ax i ia).
              by specialize (H10 i ix).
            by subst a.

            assert (a // x <> ∅).
              intro.
              apply diff_sub in H11.
              case (notax H11).
            apply not_empty in H11.
            induction H11 as [y].
            apply diff in H11.
            induction H11.
            specialize (H3 y H11).
            induction H2.
            induction H13.
            induction H14.
            specialize (H15 x y xb H3).
            move : H15.
            repeat rewrite inrel.
            intro.

            induction H15 as [xy | H15].
              induction H.
              specialize (H15 y H11).
              specialize (H15 x xy).
              case (notxa H15).
              induction H15 as [yx | xy].
                case (H12 yx).
                subst y.
                case (notxa H11).
            by exists b.
            by exists b.
            by exists b.
            by exists b.
            done.
  + intros i ia.
    induction H3 as [ab | ab].
    - induction H1.
      by specialize (H3 a ab i ia).
    - by subst b.
Qed.      


    
    
              
            

