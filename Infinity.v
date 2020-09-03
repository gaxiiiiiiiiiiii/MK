Require Export Replacement.

Definition suc x := x ∪ (Single x). 

Axiom Infinity :
  exists x, M x /\ ∅ ∈ x /\ (forall u, u ∈ x -> ((suc x) ∈ x)).

Definition Russell :=
  {| fun x => ~ x ∈ x |}.

Theorem notRussell :
  ~ M Russell.
Proof.
  intro V_.
  case (ExcludedMiddle (Russell ∈ Russell)) as [H | H].
  + pose H as H0.
    move : H0.
    rewrite classify.
    intro F.
    case (F H).
    done.
  + apply H.
    apply classify.
    done.
    done.
Qed.

