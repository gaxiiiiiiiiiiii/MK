Require Export Logics.
Require Export Coq.Setoids.Setoid.
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
Notation "x ∈ X" := (In x X) (at level 50).


Definition Equal (X Y : Class) := 
  forall Z, Z ∈ X <-> Z ∈ Y.
Notation "X ≡ Y" := (Equal X Y)(at level 5).

Axiom equal :
    forall X Y, X = Y <-> X ≡ Y.

Definition Inclusion (X Y : Class) :=
  forall Z, Z ∈ X -> Z ∈ Y.
Notation "X ⊆ Y" := (Inclusion X Y)(at level 10).

Definition ProperInclusion (X Y : Class) :=
  X ⊆ Y /\ ~(X ≡ Y).
Notation "X ⊂ Y" := (ProperInclusion X Y) (at level 10).


Definition M X :=
  exists Y , X ∈ Y.

Definition Pr X :=
  ~ M X.

Axiom Existance :
forall P, exists Z, forall x, M x -> x ∈ Z <-> P x.

Declare Scope NBG_scope.
Open Scope NBG_scope.



Axiom Classify : (Class -> Prop) -> Class.
Notation "{| P |}"  := (Classify P) (at level 10) : NBG_scope.

Axiom classify :
  forall P u, M u -> u ∈ ({|P|}) <-> P u.


Definition Empty :=
  {| fun x => x <> x|}.

Notation "∅" := (Empty).

Theorem empty x (x_ : M x):
  ~ x ∈ ∅.
Proof.
  rewrite classify.
  by apply DoubleNegative.
  auto.
Qed.  
    
Axiom empty_set :
  M ∅.

Definition V :=
  {|fun x => x = x |}.

Theorem universe x (x_ : M x):
  x ∈ V.
Proof.
  by apply classify.
Qed.  

Definition Pairing x y :=
  {| fun u => u = x \/ u = y |}.

Axiom pairing_set :
  forall x y, M x -> M y -> M (Pairing x y).

Theorem pairing x y u (u_ : M u):
  u ∈ Pairing x y <-> u = x \/ u = y.
Proof.
  by rewrite classify.
Qed.



