Require Export Axioms.


Definition Single X := 
  Pairing X X.

Theorem single X (X_ : M X):
  X ∈ Single X.
Proof.
  apply (pairing X X X X_).
  by apply or_introl.
Qed.  


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
  {| fun u => exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ X /\ y ∈ Y|}.
Notation "X × Y" := (Product X Y) (at level 10).

Theorem product X Y u :
  u ∈ X × Y <-> exists x y, M x /\ M y /\ u = <|x,y|> /\ x ∈ X /\ y ∈ Y.
Proof.
  split => [H | H].
  + assert (u_ : M u) by (by exists (X × Y)).
    by move: H; apply classify.
  + rewrite classify.
    exact H.
    induction H as [x]; induction H as [y].
    induction H as [x_]; induction H as [y_].
    induction H as [u_xy]; induction H as[xX yY].    
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

Theorem power X x (x_ : M x):
    x ∈ (Power X) <-> x ⊆ X.
Proof.
  by rewrite classify.
Qed.

Axiom power_set :
  forall x, M x -> M (Power x).

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

Axiom union_set :
  forall x, M x -> M (⊔ x).




  











