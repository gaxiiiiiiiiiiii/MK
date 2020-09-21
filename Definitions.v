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

Theorem cup X Y u :
  u ∈ (X ∪ Y) <-> u ∈ X \/ u ∈ Y.
Proof.
  split => [H | H].
  + assert (u_ : M u) by (by exists (X ∪ Y)).
    apply comple in H.
    move : H.
    rewrite cap.
    repeat rewrite comple.
    rewrite DeMorgan_notand.
    repeat rewrite DoubleNegative.
    done.
    done.
    done.
    done.
  + induction H as [uX | uY].
    - assert (u_ : M u) by (by exists X).
      apply comple.
      done.
      rewrite cap.
      repeat rewrite comple.
      apply DeMorgan_notand.
      repeat rewrite DoubleNegative.
      by apply or_introl.
      done. done.
    - assert (u_ : M u) by (by exists Y).
      apply comple.
      done.
      rewrite cap.
      repeat rewrite comple.
      apply DeMorgan_notand.
      repeat rewrite DoubleNegative.
      by apply or_intror.
      done. done.
Qed.

Definition V :=
  ∅ ^c.

Theorem universe x :
  x ∈ V <-> M x.
Proof.
  split => [H | H].
  + by exists V.
  + rewrite comple.
    by apply empty.
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



Definition Union X :=
  {| fun x => exists Y, x ∈ Y /\ Y ∈ X|}.
Notation "⊔ X" := (Union X) (at level 10).

Theorem union X x :
  x ∈ ⊔ X <-> exists Y, x ∈ Y /\ Y ∈ X.
Proof.
  split => [H | H].
  assert (x_ : M x) by (by exists (⊔ X)).
  + move : H. rewrite classify. intro H.
    induction H as [Y].
    induction H as [xY YX].
    by exists Y.
    done.
  + induction H as [Y]; induction H as [xY YX].
    rewrite classify.
    by exists Y.
    by exists Y.
Qed.

Axiom union_set :
  forall x, M x -> M (⊔ x).

Definition Caps X :=
  {|fun x => forall Y, Y ∈ X -> x ∈ Y|}.
Notation "⊓ X" := (Caps X) (at level 10).

Theorem caps X x (x_ : M x) :
    x ∈ ⊓ X <-> (forall Y, Y ∈ X -> x ∈ Y).
Proof.
  by rewrite classify.
Qed.

Theorem caps_empty :
  ⊓ ∅ = V.
Proof.
  rewrite equal => i.
  split => [H | H].
  + assert (i_ : M i) by (by exists (⊓ ∅)).
    unfold V.
    rewrite comple.
    apply empty.
    done.
    done.
  + assert (i_ : M i) by (by exists V).
    rewrite caps.
    intros Y Y0.
    assert (Y_ : M Y) by (by exists ∅).
    specialize (empty Y Y_) as emp.
    case (emp Y0).
    done.
Qed.
