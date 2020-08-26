Require Export Axioms.



Axiom InRelation :
  exists X, forall u v, M u -> M v -> <|u,v|> ∈ X <-> u ∈ v.

Axiom Intersection :
    forall X Y, exists Z, forall u, M u -> u ∈ Z <-> (u ∈ X /\ u ∈ Y).


Axiom Complement :
      forall X, exists Z, forall u, M u -> u ∈ Z <-> ~ u ∈ X.

Axiom Domain :
  forall X, exists Z, forall u, M u -> u ∈ Z <-> exists v, <|u,v|> ∈ X.

Theorem welldefine_cap X Y :
    exists !Z, forall u, M u -> u ∈ Z <-> (u ∈ X /\ u ∈ Y).
Proof.
  specialize (Intersection X Y) as H.
  induction H as [Z H].
  exists Z.
  apply (conj H).
  intros Z' H'.
  apply equal.
  intros i.
  split => [iZ | iZ'].
  + assert (i_ : M i) by (by exists Z).
    rewrite (H' i i_).
    by rewrite <- (H i i_).
  + assert (i_ : M i) by (by exists Z').
    rewrite (H i i_).
    by rewrite <- (H' i i_).
Qed.

Axiom Cap : Class -> Class -> Class.
Notation "X ∩ Y" := (Cap X Y)(at level 10).  
Axiom cap :
  forall {X Y}, forall u, u ∈ (X ∩ Y) <-> u ∈ X /\ u ∈ Y.

Theorem welldefine_complement X :
  exists !Z, forall u, M u -> u ∈ Z <-> ~ u ∈ X.
Proof.
  specialize (Complement X) as H.
  induction H as [Z H].
  exists Z.
  apply (conj H).
  intros Z_ H_.
  apply equal.  
  intros i.
  split => [iz | iz_].
  + assert (i_ : M i) by (by exists Z).
    rewrite (H_ i i_).
    by rewrite <- (H i i_).
  + assert (i_ : M i) by (by exists Z_).
    rewrite (H i i_).
    by rewrite <- (H_ i i_).
Qed.

Axiom Comple : Class -> Class.
Notation "X ^c" := (Comple X)(at level 10).  
Axiom comple :
  forall {X} u, u ∈ (X ^c) <-> ~ u ∈ X.

Theorem welldefine_dom X :
    exists !Z, forall u, M u -> u ∈ Z <-> exists v, <|u,v|> ∈ X.
Proof.
  specialize (Domain X) as H.
  induction H as [Z H].
  exists Z.  
  apply (conj H).
  intros Z_ H_.
  apply equal.
  intro i.
  split => [iz | iz_].
  + assert (i_ : M i) by (by exists Z).
    rewrite (H_ i i_).
    by rewrite <- (H i i_).
  + assert (i_ : M i) by (by exists Z_).
    rewrite (H i i_).
    by rewrite <- (H_ i i_).
Qed.


  
Axiom Dom : Class -> Class.  
Axiom dom :
  forall {X} u, M u -> u ∈ (Dom X) <-> exists v, M v /\ <|u,v|> ∈ X.
    
Definition Cup X Y :=
    ((X ^c) ∩ (Y ^c)) ^c.
Notation "X ∪ Y" := (Cup X Y) (at level 10).    

Theorem cup X Y :
  forall u, u ∈ (X ∪ Y) <-> u ∈ X \/ u ∈ Y.
Proof.
  intros u.
  unfold Cup.
  rewrite comple.
  rewrite cap.
  repeat rewrite comple.
  rewrite DeMorgan_notand.
  repeat rewrite DoubleNegative.
  done.
Qed.

Definition V :=
    ∅ ^c.

Theorem universe :
  forall u, M u -> u ∈ V.
Proof.
  intros u u_.
  rewrite comple.
  apply empty .
Qed.

Definition Diff X Y :=
  X ∩ (Y ^c).
Notation "X // Y" := (Diff X Y)(at level 10).

Theorem diff X Y :
  forall u, u ∈ (X // Y) <-> u ∈ X /\ ~ u ∈ Y.
Proof.
  intros u.
  rewrite cap.
  rewrite comple.
  done.
Qed.


Theorem cap_sym {X Y} :
  X ∩ Y = Y ∩ X.
Proof.
  apply equal.
  intro i.
  repeat rewrite cap.
  by rewrite and_comm.
Qed.  

Theorem cup_sym {X Y}:
  X ∪ Y = Y ∪ X.
Proof.
  apply equal.
  intro i.
  repeat rewrite cup.
  apply or_comm.
Qed.

Theorem cap_assoc {X Y Z} :
  (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z).
Proof.
  apply equal => i.
  repeat rewrite cap.
  apply and_assoc.
Qed.

Theorem cup_assoc {X Y Z} :
  (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z).
Proof.
  apply equal => i.
  repeat rewrite cup.
  apply or_assoc.
Qed.

Lemma and_elim {A} : 
  A /\ A <-> A.
Proof.
  split => [aa | a].
  by induction aa.
  done.
Qed.      

Theorem cap_refl {X} :
  X ∩ X = X.
Proof.
  apply equal => i.
  rewrite cap.
  by rewrite and_elim.
Qed.

Theorem cup_refl {X} :
  X ∪ X = X.
Proof.
  apply equal => i.
  rewrite cup.
  by rewrite or_elim.
Qed.

Theorem cap_empty {X} :
  X ∩ ∅ = ∅.
Proof.
  apply equal => i.
  rewrite cap.
  induction empty as [_ emp].
  specialize (emp i).
  split => [H | H].
  + apply H.
  + case (emp H).
Qed.

Theorem cup_empty {X} :
    X ∪ ∅ = X.
Proof.
  apply equal => i.
  rewrite cup.
  induction empty as [_ emp].
  specialize (emp i).
  split => [H | H].
  + induction H  as [iX | iEmp].
    - done.
    - case (emp iEmp).
  + by apply or_introl.
Qed.

Theorem cap_universe {X} :
    X ∩ V = X.
Proof.
  rewrite equal => i.
  rewrite cap.
  split => [H | H].
  + apply H.
  + apply (conj H).
    apply universe.
    by exists X.
Qed.

Theorem cup_universe {X} :
    X ∪ V = V.
Proof.
  apply equal => i.
  rewrite cup.
  split => [H | H].
  + induction H as [iX | iV].
    - apply universe.
      by exists X.
    - done.
  + by apply or_intror.
Qed.

Theorem DeMorgan_complecap {X Y} :
    (X ∩ Y) ^c = (X ^c) ∪ (Y ^c).
Proof.
  apply equal => i.
  rewrite cup.
  repeat rewrite comple.
  rewrite cap.
  by rewrite DeMorgan_notand.
Qed.

Theorem DeMorgan_complecup {X Y} :
  (X ∪ Y) ^c = (X ^c) ∩ (Y ^c).
Proof.
  apply equal => i.
  rewrite cap.
  rewrite comple.
  rewrite comple.
  rewrite comple.
  rewrite cup.
  by apply DeMorgan_notor.
Qed.

Theorem diff_self {X} :
  X // X = ∅.
Proof.
  apply equal => i.
  rewrite diff.
 split => [H | H].
  + induction H as [iX notiX].
     case (notiX iX).
  + induction empty as [_ emp].
    case ((emp i) H).
Qed.

Theorem diff_comple {X} :
    V // X = (X ^c).
Proof.
  apply equal => i.
  rewrite diff.
  rewrite comple.
  split => [H | H].
  + by induction H.
  + specialize ((proj2 empty) i) as emp.
    by rewrite comple.
Qed. 

Theorem double_comple {X} :
    (X ^c) ^c = X.
Proof.
  apply equal => i.
  repeat rewrite comple.
  apply DoubleNegative.
Qed.

Theorem universe_comple :
  V ^c = ∅.
Proof.
  apply double_comple.
Qed.

Theorem cap_dist_cap {X Y Z} :
  X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z).
Proof.
  apply equal => i.
  repeat rewrite cup.
  repeat rewrite cap.
  rewrite cup.
  split => [H | H].
  + induction H as [x H].
    induction H as [y | z].
    - by apply or_introl.
    - by apply or_intror.
  + induction H as [xy | xz]  .
    - induction xy as [x y].
      apply (conj x (or_introl y)).
    - induction xz as [x z].
      apply (conj x (or_intror z)).
Qed.







