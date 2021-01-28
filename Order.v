Require Export Segment.


Definition Ord X :=
    We E X /\ Trans X.

Definition On :=
  {| Ord |}.  


Theorem on_ord x (x_ : M x) :
    x ∈ On <-> Ord x.
Proof.
  by rewrite in_cls.
Qed.

Theorem RelE :
  Rel E.
Proof.
  move => p H.
  have p_ : M p by is_set.
  move /(in_cls _ p p_) : H => [x [y [x_ [y_ [p_xy xy]]]]].
  apply in_cls => //.
  exists x; exists y.
  by rewrite !in_universe.
Qed.  





Theorem empty_on : 
  ∅ ∈ On.
Proof.
  move : empty_set => e_.
  rewrite  on_ord => //.  
  split.
  + split => [|Y [Ye F]].
    - split.
      * apply RelE.
      * move => x F.
        have x_ : M x by is_set.
        case (notin_empty x x_ F).
    - move /not_empty : F => [y yY].
      move : (Ye y yY) => F.
      have y_ : M y by is_set.
      case (notin_empty y y_ F).
  + move => x F.
    have x_ : M x by is_set.
    case (notin_empty x x_ F).
Qed.    


Theorem ord_notrefl X:
  Ord X  -> ~ X ∈ X.
Proof.
  move => [[[RelE irr] we] H] XX.
  have X_ : M X by is_set.
  have XX_ : X ∈ X by auto.
  move : XX_.
  rewrite -orderd_in_E => //.
  by apply irr.
Qed.




Theorem ord_ele_notrefl X :
  Ord X -> forall x, x ∈ X -> ~ x ∈ x.
Proof.
  intros [[[RelE irr] we] H] x xX xx.
  have x_ : M x by is_set.
  apply (irr x xX).
  by apply orderd_in_E => //.
Qed.



Theorem ord_in_on X Y :
    Ord X -> Y ∈ X -> Y ∈ On.
Proof.
  move => [[[RelE irrX] weX] traX] YX.
  have trX : Tr E X by apply we_tr.
  move  : trX => [_ trX].
  suff weY : We E Y.
  + apply on_ord.
    is_set.
    split => //.
    move  => Z ZY i iZ.
    move : (traX Y YX) => Y_X.
    move : (Y_X Z ZY) => ZX.
    move : (traX Z ZX) => Z_X.
    move : (Z_X i iZ) => iX.
    have Y_ : M Y by is_set.
    have Z_ : M Z by is_set.
    have i_ : M i by is_set.
    apply orderd_in_E => //.
    apply (trX i Z Y).
    move /(orderd_in_E i Z i_ Z_) : iZ => iZ.
    move /(orderd_in_E Z Y Z_ Y_) : ZY => ZY.
    done.
  + split => //.
    - split => //.
      move => y yY.
      apply irrX.
      apply (traX Y) => //.
    - move => Z [ZY _Z].
      have ZX : Z ⊂ X.
        apply sub_trans with (Y := Y) => //.
        apply traX => //.
      apply weX  => //.
Qed.





Theorem trans_on :
  Trans On.
Proof.
  move => a a_On z za.
  have a_ : M a by is_set.
  move /(on_ord a a_) : a_On => [wea Tra].
  move : (we_tot  wea) => [[relE tra] [[_ irra] [_ cona]]].
  have z_ : M z by is_set.
  apply on_ord => //.
  split.
  + apply we_sub with (X := a) => //.
    apply Tra => //. 
  + move => y  yz x xy.
    have x_ : M x by is_set.
    have y_ : M y by is_set.
    move : (Tra z za y yz) => ya.
    move : (Tra y ya x xy) => xa.
    rewrite -(orderd_in_E x z x_ z_).
    apply tra with (y := y).
    rewrite !orderd_in_E => //.
Qed.

Theorem cap_ord X Y :
  Ord X -> Ord Y -> Ord (X ∩ Y).
Proof.
  move => [weX TrX] [weY TrY].
  split.
  + apply we_sub with (X := X) => //.
    apply cap_sub_l.
  + apply cap_trans => //.
Qed.

Theorem ord_subin X Y :
  Ord X -> Ord Y -> X ⊂ Y <-> (X ∈ Y) \/ X = Y.
Proof.
  move => [weX TrX] [weY TrY].
  split => [X_Y | [XY | XY]].
  + case (classic (X = Y)) => [XY|_XY]; [right|left] => //.
    pose Z := Y ~ X.
    have _Z : Z <> ∅ by apply diff_sub.
    have ZY : Z ⊂ Y.
      move => i iZ.
      have i_ : M i by is_set.
      by move /diff : iZ => [iY _].
    inversion  weY as [[_ irrY] wey].
    move : (wey Z (conj ZY _Z)) => [m [mZ Hm]].
    have m_ : M m by is_set.
    suff Xm : X = m.
    - subst m.
      apply ZY => //.
    - move /diff : mZ => [mY _mX].
      equal => i.
      move : (we_tot weY) => [[_ trY] [_ [_ conY]]].
      split => [iX|im]; have i_ : M i by is_set.
      * move : (X_Y i iX) => iY.        
        case (classic (m = i)) => [mi | _mi].
        (***)
          subst i.
          case (_mX iX).
        (***)
          case : (conY m i (conj mY (conj iY _mi))) => [mi |im].
          (***)
            move /(orderd_in_E m i m_ i_) : mi => mi.
            move : (TrX i iX m mi) => mX.
            case (_mX mX).
          (***)
            rewrite -orderd_in_E => //.
      * have m_X : m ⊂ X.
          move => j jm.
          move : (TrY m mY j jm) => jY.
          move : (Hm j) => Hj.
          case /imply_to_or : Hj => [H0|H0].
            case /not_and_or : H0 => H0.
              apply NNPP => F; apply H0.
              apply diff => //.
              apply NNPP => F; apply H0 => i_m.
              subst j.
              apply (irrY m mY).
              rewrite orderd_in_E => //.
              move : H0 => [_ _im].
              have j_ : M j by is_set.
              move /(orderd_in_E j m j_ m_):_im => _im.
              case (_im jm).
        apply m_X => //.
  + move => i iX.
    apply (TrY X XY i iX).
  + by subst X.
Qed.    
        
        



      
        


    





          

          

           