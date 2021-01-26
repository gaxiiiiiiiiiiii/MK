Require Export Similarity.

Definition E :=
    {| fun i => exists x y, M x /\ M y /\ i = <|x,y|> /\ x ∈ y|}.

Definition Trans X :=
  forall x, x ∈ X -> x ⊂ X.

    
Definition Sect R X Z :=
  Z ⊂ X /\ (forall u v, u ∈ X -> v ∈ Z -> <|u,v|> ∈ R -> u ∈ Z).

Definition Seg R X U :=
  {: X | fun x => <|x,U|> ∈ R:}.


Goal forall X, Trans X <-> (forall u v, u ∈ v /\ v ∈ X -> u ∈ X).
  Proof.
    intro X.
    split => [H u v [uv vX]| H x xX i ix].
    + by apply (H v).
    + by apply (H i x).
Qed.       
  
Theorem trans_cupssub X :
    Trans X <-> ⊔ X ⊂ X.
Proof.
  split => [H i iUX| H x xX i ix ].
  + move /(in_cups) : iUX => [Y [iY YX]].
    by apply (H Y).
  + apply H.
    apply in_cups.
    by exists x.
Qed.

Theorem cap_trans X Y :
    Trans X -> Trans Y -> Trans (X ∩ Y).
Proof.  
  move =>  HX HY U UXY i iU.
  move /in_cap : UXY => [UX UY].
  move : (HX U UX i iU) => iX.
  move : (HY U UY i iU) => iY.
  apply in_cap => //.
Qed.

Theorem cup_trans {X Y}:
    Trans X -> Trans Y -> Trans (X ∪ Y).
Proof.
  move =>  HX HY U UXY i iU.
  case /in_cup : UXY => [UX | UY]; apply in_cup; [left|right].
  + by apply (HX U).
  + by apply (HY U).
Qed.

Theorem orderd_in_E x y (x_: M x) (y_ : M y) :
    <|x,y|> ∈ E <-> x ∈ y.
Proof.
  have xy_ : M <|x,y|>.
    by apply orderd_set.
  split => [H|H].
  + move /(in_cls _ _ xy_) : H => [a [b [a_ [b_ [xyab ab]]]]].
    move /(orderd_eq x y a b x_ y_ a_ b_) : xyab => [xa yb].
    by subst a b.
  + apply in_cls => //.
    by exists x; exists y.
Qed.    


Theorem segE_cap X u (u_ : M u) :
    Seg E X u = X ∩ u.
Proof.
  equal => i.
  split => [H | H]; have i_ : M i by is_set.
  + move /(in_cls _ _ i_) : H => [iX iu_E].
    move /(orderd_in_E i u i_ u_) : iu_E => iu.
    by apply in_cap.
  + move /in_cap : H => [iX iu].
    apply in_cls => //.
    split => //.
    apply orderd_in_E => //.
Qed.

Theorem cap_sub_l a b :
  (a ∩ b) ⊂ a.
Proof.
  move => i Hi.
  by move /in_cap : Hi => [ia ib].
Qed.

Theorem cap_sub_r a b :
  (a ∩ b) ⊂ b.
Proof.
  move => i Hi.
  by move /in_cap : Hi => [ia ib].
Qed.




Theorem segE_set X u (u_ : M u):
    M (Seg E X u).
Proof.
  apply (sub_set _ u) => //.
  rewrite segE_cap => //.
  apply cap_sub_r.
Qed.

Theorem trans_seg {X} :
  Trans X <-> forall u, M u -> u ∈ X -> Seg E X u = u.
Proof.
  split => [H u u_ uX|H u uX i iu].
  + rewrite segE_cap => //.
    equal => i.
    split => [iXu|iu]; have i_ : M i by is_set.
    - by move /in_cap : iXu => [_ iu].
    - apply in_cap.
      split => //.
      by apply (H u).
  + have u_ : M u by is_set.
    rewrite  -(H u u_ uX) in iu.
    rewrite segE_cap in iu => //.
    by move /(in_cap) : iu => [iX _].
Qed.  

Theorem diff_sub X Y :
  X <> Y -> X ⊂ Y-> Y ~ X <> ∅.
Proof.
  move => _XY XY F.

  apply _XY.
  equal => i.
  split => [iX | iY]; have i_ : M i by is_set.
  + apply XY => //.
  + move : (notin_empty i i_) => _i.
    rewrite -F in _i.
    apply NNPP => _iX.
    apply _i.
    apply diff => //.
Qed.      

 


Theorem we_sect_seg X Z :
  We E X -> Sect E X Z -> Z <> X -> exists u, u ∈ X /\ Z = Seg E X u.
Proof.
  move => [[RelE irrX] weX] [ZX sect] _ZX.
  have we : We E X by auto.
  move : (we_con we) => [_ con].
  move : (we_tr we) => [_ tr].
  clear we.

  pose Y := X ~ Z.
  have _Y : Y <> ∅ by apply diff_sub => //.
  have YX : Y ⊂ X.
    move => i iY.
    by move /diff : iY => [iX _].
  move : (weX Y (conj YX _Y)) => [m [mY Hm]].
  have m_ : M m by is_set.
  move /diff : mY => [mX _mZ].

  exists m; split => //.
  rewrite segE_cap => //.
  equal => i.
  split => [iZ |iXm]; have i_ : M i by is_set.
  + apply in_cap; split.
    - apply ZX => //.
    - have iX : i ∈ X by apply ZX => //.      
      case (classic (i = m)) => [im | _im].
      * subst i.
        case (_mZ iZ).
      * case (con i m (conj iX (conj mX _im))) => [im|mi].
        by apply orderd_in_E.
        move : (sect m i mX iZ).
        case /imply_to_or => [_mi | mZ].
          case (_mi mi).
          case (_mZ mZ).
  + move /in_cap : iXm => [iX im].
    apply NNPP => F.
    have iY : i ∈ Y by apply diff => //.
    case (classic (i = m)) => [i_m|_im] .
    - subst m.
      move : im; rewrite -orderd_in_E => //; apply irrX => //.
    - move : (Hm i (conj iY _im)).
      rewrite !orderd_in_E => //=> [mi _i_m].
      case (_i_m im).
Qed.     