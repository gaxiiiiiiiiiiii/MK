Require Export Axioms.
Require Export Classical.


Definition Single X := 
  Pair X X.  

Theorem in_single X Y (Y_ : M Y) :
  Y ∈ Single X <-> Y = X.
Proof.
  split; rewrite in_pair => // H.
  + by case H.
  + by left.
Qed. 

Theorem single_set X :
    M X -> M (Single X).
Proof.
  move => X_.
  apply pair_set => //.
Qed.        


Definition Orderd X Y:= Pair (Single X) (Pair X Y).
Notation "<| a , b , .. , d |>" := (Orderd .. (Orderd a b) .. d)(at level 0).

Theorem orderd_set X Y (X_ : M X) (Y_ : M Y) :
  M (<|X,Y|>).
Proof.
  apply pair_set.
  by apply pair_set.
  by apply pair_set.
Qed.  

Definition InRel :=
  {|fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ y|}.

Ltac is_set := unfold M; eauto.  

Theorem inrel u :
  u ∈ InRel <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ y.
Proof.
  split => [H|[x [y [x_ [y_ [u_xy xy]]]]]].
  + have u_ : M u by is_set.
    by move /(in_cls _ _ u_) : H.
  + subst u.
    apply in_cls.
    apply orderd_set => //.
    by exists x; exists y.
Qed.

Definition Intersection X Y :=
  {|fun u => u ∈ X /\ u ∈ Y|}.
Notation "X ∩ Y" := (Intersection X Y)  (at level 60).

Theorem in_cap X Y u :
    u ∈ (X ∩ Y) <->  u ∈ X /\ u ∈ Y.
Proof.
  split => [H | H].
  + assert (u_ : M u) by is_set.
    move /in_cls : H.
    by apply.
  + move : H => [uX uY].
    rewrite in_cls => //.
    is_set.
Qed.   


Definition Comple X := 
  {| fun x => ~ x ∈ X|}.
Notation "¬ X" := (Comple X)(at level 5).

Theorem in_comp X x (x_ : M x):
    x ∈ ¬X <-> ~ x ∈ X.
Proof.
  by rewrite in_cls.
Qed.



Definition Cup X Y :=
  ¬(¬X ∩ ¬Y).
Notation "X ∪ Y" := (Cup X Y) (at level 10).    

Theorem in_cup X Y u :
  u ∈ (X ∪ Y) <-> u ∈ X \/ u ∈ Y.
Proof.
  split => [H | H].
  + have u_ : M u by is_set.
    move /(in_comp _ _ u_) : H.
    move /in_cap.
    move /not_and_or.
    by case; move /(in_comp _ _ u_) => H; [left|right]; apply NNPP.
  + case H => [uX|uY]; have u_ : M u by is_set.
    - rewrite in_comp => //.
      rewrite in_cap.
      apply or_not_and.
      left.
      by rewrite in_comp.
    - rewrite in_comp => //.
      rewrite in_cap.
      apply or_not_and.
      right.
      by rewrite in_comp.
Qed.




Definition V :=
  ¬∅.

Theorem in_universe x :
  x ∈ V <-> M x.
Proof.
  split => [H | H].
  + by exists V.
  + rewrite in_comp => //.
    by apply notin_empty.
Qed.









Definition Dom f :=
  {| fun x => exists y, M y /\ <|x,y|> ∈ f|}.

Theorem in_dom f x (x_ : M x):
  x ∈ Dom f <-> exists y, M y /\ <|x,y|> ∈ f.
Proof.
  by rewrite in_cls.
Qed.

Definition Ran f := 
  {|fun y => exists x, M x /\ <|x,y|> ∈ f|}.

Theorem in_ran f y (y_ : M y) :
  y ∈ Ran f <-> exists x, M x /\ <|x,y|> ∈ f.
Proof.
  by rewrite in_cls.
Qed.

Definition Diff X Y :=
  {| fun u => u ∈ X /\ ~ u ∈ Y|}.
Notation "X ~ Y"  := (Diff X Y) (at level 10).

Theorem diff X Y u :
  u ∈ X ~ Y <-> u ∈ X /\ ~ u ∈ Y.
Proof.
  split => [H | [uX _uY]]; have u_ : M u by is_set.
  + by move /(in_cls _ _ u_) : H.
  + by rewrite in_cls. 
Qed.



Definition Product X Y :=
  {| fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ X /\ y ∈ Y|}.
Notation "X × Y" := (Product X Y) (at level 10).

Theorem in_prod X Y u :
  u ∈ X × Y <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ X /\ y ∈ Y.
Proof.
  split => [uXY | [x [y [x_ [y_ [u_xy [xX yY]]]]]]].
  + have u_ : M u by is_set.
    move /in_cls : uXY; auto.
  + rewrite in_cls.
    by exists x; exists y.
    by subst u; apply orderd_set.
Qed.


Definition Sq X := X × X.
Notation "X ²" := (Sq X)(at level 1).

Definition Rel X := X ⊆ V².

Definition Power X :=
  {| fun x => x ⊂ X|}.

Theorem in_pow X x (x_ : M x):
    x ∈ (Power X) <-> x ⊂ X.
Proof.
  by rewrite in_cls.
Qed.

Axiom pow_set :
  forall x, M x -> M (Power x).



Definition Cups X :=
  {| fun x => exists Y, x ∈ Y /\ Y ∈ X|}.
Notation "⊔ X" := (Cups X) (at level 10).

Theorem in_cups X x :
  x ∈ ⊔ X <-> exists Y, x ∈ Y /\ Y ∈ X.
Proof.
  split => [H | [Y [xY YX]]].
  + have x_ : M x  by is_set.
    move /in_cls : H; auto.
  + rewrite in_cls.
    by exists Y.
    is_set.
Qed.

Axiom cups_set :
  forall x, M x -> M (⊔ x).

Definition Caps X :=
  {|fun x => forall Y, Y ∈ X -> x ∈ Y|}.
Notation "⊓ X" := (Caps X) (at level 10).

Theorem in_caps X x (x_ : M x) :
    x ∈ ⊓ X <-> (forall Y, Y ∈ X -> x ∈ Y).
Proof.
  by rewrite in_cls.
Qed.

Theorem caps_empty__universe :
  ⊓ ∅ = V.
Proof.  
  rewrite -Equal => i.
  split => [H | H]; have i_ : M i by is_set.
  + by apply in_universe.
  + rewrite in_caps => // Y HY.
    have Y_ : M Y by is_set.
    case (notin_empty Y Y_ HY).
Qed.
