Require Export Logics.
Require Export Coq.Setoids.Setoid.

Lemma or_elim {A} :
  A \/ A <-> A.
Proof.
  split => [aa | a].
  induction aa.
  done.
  done. 
  by apply or_introl.
Qed.


(* 4.1 An Axiom systems*)

Axiom Class : Type.
Axiom In : Class -> Class -> Prop.
Notation "x ∈ X" := (In x X) (at level 10).




Definition Equal (X Y : Class) := 
  forall Z, Z ∈ X <-> Z ∈ Y.
Notation "X ≡ Y" := (Equal X Y)(at level 10).

Axiom equal :
    forall X Y, X = Y <-> X ≡ Y.

Definition Inclusion (X Y : Class) :=
  forall Z, Z ∈ X -> Z ∈ Y.
Notation "X ⊆ Y" := (Inclusion X Y)(at level 10).

Definition ProperInclusion (X Y : Class) :=
  X ⊆ Y /\ ~(X ≡ Y).
Notation "X ⊂ Y" := (ProperInclusion X Y) (at level 10).

(* Proposition 4.1 *)

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



Definition M X :=
  exists Y , X ∈ Y.

Definition Pr X :=
  ~ M X.



Theorem Extensionality :
    forall X Y, M X -> M Y -> X ≡ Y <-> (forall z, M z -> z ∈ X <-> z ∈ Y).
Proof.
  intros X Y MX MY.
  split => [XY z Mz| H].
  apply XY.
  intro z.  
  split => [zX | zY].
  + assert (Mz : M z).
    by exists X.
    by apply  (H z Mz) in zX.
  + assert (Mz : M z).
    by exists Y.
    by apply (H z Mz) in zY.
Qed.    


Axiom T :
    forall {X Y}, X ≡ Y -> (forall Z, X ∈ Z <-> Y ∈ Z).

Theorem M_eq X Y :
  M X /\ X ≡ Y -> M Y.
Proof.
  intro H.
  induction H as [MX XY].
  induction MX as [U XU].
  exists U.
  by apply (T XY).
Qed.

Axiom P :
  forall X Y, M X -> M Y -> 
  exists U, M U /\ 
  (forall u, M u ->  (u ∈ U <-> (u ≡ X \/ u ≡ Y))).


Theorem unique_pair :
  forall x y, M x -> M y -> exists !U, M U /\ (forall u, M u ->  (u ∈ U <-> (u ≡ x \/ u ≡ y))).
Proof.
  intros x y X_ Y_.
  specialize (P x y X_ Y_) as H.
  induction H as [U H].
  induction H as [U_ H].
  exists U.
  apply (conj (conj U_ H)).
  intros U' H'.
  induction H' as [U'_  H'].
  apply equal.
  intro u.
  split => [uU | uU'].
  + assert (u_ : M u) by (by exists U).
    specialize (H u u_).
    specialize (H' u u_).
    rewrite H'.
    by rewrite <- H.
  + assert (u_ : M u) by (by exists U').
    rewrite (H u u_).
    by rewrite <- (H' u u_).
Qed.

Axiom N :
  exists x, M x /\ (forall y, M y -> ~ y ∈ x).


Theorem exists_empty :
 exists !e, M e /\ forall y, M y -> ~ y ∈ e.
Proof.
  induction N as [e H].
  exists e.
  apply (conj H).
  intros e' H'.
  induction H as [e_ H].  
  induction H' as [e'_ H'].
  apply equal.
  intro i.
  split => [ie | ie'].
  + assert (i_ : M i) by (by exists e).
    case ((H i i_) ie).
  + assert (i_ : M i) by (by exists e').
    case ((H' i i_) ie').
Qed.    

Axiom Empty : Class.
Notation "∅" := (Empty).

Axiom empty :
    M ∅ /\ forall y, ~ y ∈ ∅.

Theorem exists_pair X Y:
    exists !Z, (( ~ M X \/ ~ M Y) /\ Z = ∅) \/ 
               (M X /\ M Y /\ (forall u, M u ->u ∈ Z <-> (u ≡ X \/ u ≡ Y))).
Proof.
  case (ExcludedMiddle (M X /\ M Y)) as [XY_ | notXY_].
  + induction XY_ as [X_ Y_] .
    specialize (P X Y X_ Y_) as Hp.
    induction Hp as [P H].
    induction H as [P_ H].
    exists P.
    split.
    apply (or_intror (conj X_ (conj Y_ H))).
    intros P' H'.
    induction H' as [L | R].
    - induction L as [notXY_ _].
      apply DeMorgan_notand in notXY_.
      case (notXY_ (conj X_ Y_)).
    - induction R as [_ R]; induction R as [_ H'].
      apply equal.
      intro u.
      split => [xP | xP'].
      * assert (u_ : M u) by (by exists P).
        rewrite (H' u u_).
        by rewrite <- (H u u_).
      * assert (u_ : M u) by (by exists P').
        rewrite (H u u_).
        by rewrite <- (H' u u_).
  + apply DeMorgan_notand in notXY_.
    exists ∅.
    split.
    - by apply or_introl.
    - intros z H.
      induction H as [H | H].
      * by induction H.
      * induction H as [X_]; induction H as [Y_ _] .
        induction notXY_ as[notX_ | notY_].
        case (notX_ X_).
        case (notY_ Y_).
Qed.        

Axiom NOP : Class -> Class -> Class.

Axiom  nop: forall X Y, 
  (( ~ M X \/ ~ M Y) /\ (NOP X Y) = ∅) \/ 
  (M X /\ M Y /\ (forall u, M u ->u ∈ (NOP X Y) <-> (u ≡ X \/ u ≡ Y))).

Theorem nop_set X Y :
  M (NOP X Y).
Proof.
  induction (nop X Y) as [H | H].
  + induction H as [_ H].
    rewrite H.
    by induction empty.
  + induction H as [X_]; induction H as [Y_].
    specialize (P X Y X_ Y_) as H0.
    induction H0 as [U]; induction H0 as [U_].
    assert (U_XY : U ≡ (NOP X Y)).
    - intro i.
      case (ExcludedMiddle (M i)) as [i_ | noti_].
      * rewrite (H i i_).
        by rewrite <- (H0 i i_).
      * split => [H1 | H1].
        assert (i_ : M i) by (by exists U).
        case (noti_ i_).
        assert (i_ : M i) by (by exists (NOP X Y)).
        case (noti_ i_).
    - apply equal in U_XY.
      by rewrite <- U_XY.
Qed.


Theorem Pair (x y u : Class) (x_ : M x) (y_ : M y) (u_ : M u) :
  u ∈ (NOP x y) <-> u ≡ x \/ u ≡ y.
Proof.
  induction (nop x y).
  + induction H as [F  _].
    apply DeMorgan_notand in F.
    case (F (conj x_ y_)) .
  + induction H as [_]; induction H as [_].
    by specialize (H u u_).
Qed.

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




      







    



    

    

    


  








