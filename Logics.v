Require Export ssreflect.

Axiom ExcludedMiddle :
  forall P, P \/ ~ P.

Theorem DoubleNegative (P : Prop) :
  ~~ P <-> P.
Proof.
  split.
  + intro notP.
    case (ExcludedMiddle P) as [p  | notp].
  - apply p.
  - case (notP notp).
    + intros p notp.
      apply (notp p).
Qed.

Theorem DeMorgan_notand (A B : Prop) :
  ~ (A /\ B) <-> ~ A \/ ~ B.
Proof.
  split => [H | H].
  + case (ExcludedMiddle A) as [a | nota].
  - apply or_intror.
    intro b.
    apply (H (conj a b)).
  - apply (or_introl nota).
    + intro ab.
      induction ab as [a b].
      induction H as [nota | notb].
  - apply (nota a).
  - apply (notb b).
Qed.

Theorem DeMorgan_notor (A B : Prop) :
  ~ (A \/ B) <-> ~ A /\ ~ B.
Proof.
  split => [H | H].
  + split.
  - intro a.
    apply (H (or_introl a)).
  - intro b.
    apply (H (or_intror b)).
    + induction H as [nota notb].
      intro ab.
      induction ab as [a | b].
  - apply (nota a).
  - apply (notb b).
Qed.

Theorem contrapositive (A B : Prop) :
  (A -> B) <-> (~ B -> ~ A).
Proof.
  split => [H | H].
  + intros notb a.
    apply (notb (H a)).
  + intro a.
    apply DoubleNegative.
    intro notb.
    apply ((H notb) a).
Qed.

Theorem notall_existsnot (X : Type) (P : X -> Prop) :
  ~ (forall x, P x) <-> exists x, ~ P x.
Proof.
  split.
  + apply contrapositive.
    intros H.
    apply DoubleNegative.
    intro x.
    case (ExcludedMiddle (P x)) as [Px | notPx ].
    - done.
    - assert (Px : exists x, ~ P x).
      * exists x.
        apply notPx.
      * case (H Px).
+ intros H allPx.
  induction H as [x notPx].
  specialize (allPx x) as Px.
  apply (notPx Px).
Qed.


Theorem allnot_notexists (X : Type) (P : X  -> Prop) :
  (forall x, ~ P x) <->  ~ exists x, P x.
Proof.
  split.
  + apply contrapositive.
    intro H.
    apply (DoubleNegative (exists x, P x)) in H.
    apply (notall_existsnot X (fun x => ~ P x)).
    induction H as [x Px].
    exists x.
      by apply DoubleNegative.
  + intros H x Px.
    apply H.
    exists x.
    apply Px.
Qed.




Theorem implicate {A B : Prop}:
  (A -> B) <-> (~ A \/ B).
Proof.
  split => [H | H a].
  + case (ExcludedMiddle A) as [a | nota].
    - apply (or_intror (H a)).
    - apply (or_introl nota).
  + induction H as [nota | b].
    - case (nota a).
    - done.
Qed.    
