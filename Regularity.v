Require Export Segment.

Axiom Regularity :
  forall X, X <> ∅ -> exists x, x ∈ X /\ x ∩ X = ∅.