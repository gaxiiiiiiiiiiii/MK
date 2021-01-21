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
Notation "x ∈ X" := (In x X) (at level 50).


Axiom Equal : forall X Y,
  (forall Z, Z ∈ X <-> Z ∈ Y) <-> X = Y.


Definition Inclusion (X Y : Class) :=
  forall Z, Z ∈ X -> Z ∈ Y.
Notation "X ⊂ Y" := (Inclusion X Y)(at level 10).


Definition ProperInclusion (X Y : Class) :=
  X ⊂ Y /\ X <> Y.
Notation "X ⊆ Y" := (ProperInclusion X Y) (at level 10). 



Definition M X :=
  exists Y , X ∈ Y.

Definition Pr X :=
  ~ M X.


Axiom Classify : (Class -> Prop) -> Class.
Notation "{| P |}"  := (Classify P) (at level 0).

Axiom in_cls :
  forall P u, M u -> u ∈ ({|P|}) <-> P u.

Axiom Empty : Class.
Notation "∅" := (Empty).

Axiom notin_empty :
  forall x, M x -> ~ x ∈ ∅.
    
Axiom empty_set :
  M ∅.

 
Definition Pair x y :=
  {| fun u => u = x \/ u = y |}.

Axiom pair_set :
  forall x y, M x -> M y -> M (Pair x y).

Theorem in_pair x y u (u_ : M u):
  u ∈ Pair x y <-> u = x \/ u = y.
Proof.
  rewrite in_cls => //.
Qed.





