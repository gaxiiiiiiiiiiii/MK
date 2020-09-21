Require Export Order.

Theorem suc_ X x (X_ : M X):
  x ∈ suc X <-> x ∈ X \/ x = X.
Proof.
  rewrite cup.
  split => [H | H].
  + induction H as [xX | xX].
    - by apply or_introl.
    - assert (x_ : M x) by (by exists (Single X)) .
      apply (in_single x X x_ X_) in xX.
      by apply or_intror.
  + induction H as [H |  H]  .
    - by apply or_introl.
    - subst x.
      apply or_intror.
      by apply single.      
Qed.


Definition Natural n :=
  n ∈ ON /\ (forall x, x ∈ n \/ x = n -> x = ∅ \/ exists y, M y /\ x = suc y).

Theorem suc_natural x :
  x <> ∅ -> Natural x -> Natural (⊔ x).
Proof.
  intros x0 H.
  induction H.
  split.
  + by apply union_on.
  + intros i i_x.
    induction i_x.
    - apply union in H1.
      induction H1 as [y].
      induction H1 as [iy yx].
      assert (x_ : M x) by (by exists ON).
      apply (on x x_) in H.
      induction H.
      specialize ((H y yx) i iy).
      by specialize (H0 i (or_introl H)).
    - 
Qed.    



Theorem union_sub x (xON : x ∈ ON) :
  ⊔ x ⊆ x.
Proof.
  intros i Hi.
  apply union in Hi.
  induction Hi as [y].
  induction H as [iy yx].
  assert (x_ : M x) by (by exists ON).
  apply (on x x_) in xON.
  induction xON.
  by specialize ((H y yx) i iy).
Qed.  


Theorem union_diff x (xNat : Natural x) :
  x <> ∅ -> x // (⊔ x) = Single (⊔ x).
Proof.
  intro x0.
  induction xNat.
  apply equal => i.
  rewrite diff.
  split => [H1 | H1].
  + induction H1.
    rewrite in_single.
    apply equal => j.








Theorem union_sup x (xON : x ∈ ON) :
  forall a, a ∈ x -> forall b, a ∈ b \/ a = b -> ⊔ x ∈ b \/ ⊔ x = b.
Proof.
  intros a ax b H.
  induction H as [ab | ab].
  + Show 
      








Theorem suc_union x (xON : x ∈ ON) :
  x <> ∅ -> Natural x -> suc (⊔ x) = x.
Proof.
  intros x0 H.
  assert (x_ : M x) by (by exists ON).
  apply (on x x_) in xON as xON_.
  assert (Natural x) as Nat_x by done.
  induction H as [_ H].
  apply not_empty in x0 as x0_.
  induction x0_ as [i ix].
  apply (H i) in ix as H0.
  apply equal => j.
  split => [H1 | H1].
  + apply suc_ in H1.
    induction H1.
    - apply union in H1.
      induction H1 as [y]; induction H1 as [jy yx].
      induction xON_.
      by specialize ((H1 y yx) j jy).
    - subst j.
      specialize (suc_natural x x0 Nat_x) as H1.
      induction H1.
      specialize (on_tri x (⊔ x) xON H1) as H3.
      induction H3.
      * apply union in H3.
        induction H3 as [y].
        induction H3 as [xy yx].
        induction xON_.
        specialize ((H3 y yx) x xy).
        apply (on x x_) in xON.
        specialize (on_notrefl x xON) as F.
        case (F H3).
      * induction H3.
        done.
        (* apply equal in H3.
        specialize (H3 i).
        induction H3 as [H3 _].
        specialize (H3 ix).
        apply union in H3.
        induction H3 as [j].
        induction H3 as [ij jx].
        apply (H j) in jx as H3.
        induction H3.
          subst j.
          assert (i_ : M i) by (by exists ∅).
          case ((empty i i_) ij).
          induction H3 as [y].
          induction H3 as [y_ j_y].
          subst j. *)


        assert (i_x : i ∈ x) by done.
        rewrite H3 in ix.
        apply union in ix.
        induction ix as [y].
        induction H4 as [iy yx].
        apply (H y) in yx as y_x.



    



    
Theorem natural n  :
  Natural n -> Natural (suc n) /\ (forall x, x ∈ n -> Natural x).
Proof.
  intro H.
  induction H as [nON H].
  assert (n_ : M n) by (by exists ON).
  split.
  + split.
    - apply (suc_on n nON).
    - intros x x_.
      apply (suc_ n x n_) in x_.
      induction x_ as [nx | nx].
      * by specialize (H x nx).
      * subst x.
        case (ExcludedMiddle (n = ∅)) as [H0 | H0].
          (* n = ∅*)
          by apply or_introl.
          (* N <> ∅*)
          apply or_intror.
          exists (⊔ n).
          split.
          by apply union_set.
          apply equal => i.
          split => [H1 | H1].
            (* i ∈ n *)
            apply (H i) in H1 as H2.
            apply not_empty in H0.
            induction H0 as [j H0].
            apply (H j) in H0 as H3.
            apply (on n n_) in nON.
            induction nON.
            induction H5.
            induction H5.            
            induction H7.
            induction H8.
            specialize (H9 i j H1 H0).            
            apply suc_.
            by apply union_set.
            clear H5 H7 H8 H6.
            assert (i_ : M i) by (by exists n).
            assert (j_ : M j) by (by exists n).
            move : H9.
            rewrite (inrel i j i_ j_).
            rewrite (inrel j i j_ i_).
            intro.
            induction H5 as [ij |].
              (* i ∈ j *)
              induction  H3 as [j0 | H3].
                (* j = ∅ *)
                subst j.
                case ((empty i i_) ij).
                (* H3 *)
                induction H3 as [k H3].
                induction H3 as [k_ H3].
                subst j.
                apply (suc_ k i k_) in ij.
                induction ij.
                  (* i ∈ k *)
                  apply or_introl.
                  apply union.
                  exists (suc k).
                  split.
                  apply (suc_ k i k_).
                  by apply or_introl.
                  done.
                  (* i = k *)
                  subst k.
                  apply or_introl.
                  apply union.
                  exists (suc i).
                  split.
                  apply (suc_ i i i_).
                  by apply or_intror.
                  done.
              induction H5 as [ji | ji].
                (* j ∈ i *)
                induction H2 as [i0 | H2].
                  (* i = ∅ *)
                  subst i.
                  case ((empty j j_) ji).
                  (* H2 *)
                  induction H2 as [k]; induction H2 as [k_].
                  subst i.
                  specialize (H (suc k) H1).
                  induction H as [F | H].
                    (* suc k = ∅ *)
                    assert (k ∈ suc k).
                      apply (suc_ k k k_).
                      by apply or_intror.
                    rewrite F in H.
                    case ((empty k k_) H).
                    (* H *)
                    induction H as [l]; induction H as [l_].



                  






            