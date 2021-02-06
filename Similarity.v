Require Export Composition.




Definition Irr R A :=
  Rel R /\ forall x, x ∈ A -> ~ <|x,x|> ∈ R.

Definition Tr R A :=
  Rel R /\ 
  forall x y z, x ∈ A /\ y ∈ A /\ z ∈ A /\ 
  <|x,y|> ∈ R /\ <|y,z|> ∈ R -> 
  <|x,z|> ∈ R.

Definition Part R A :=
  Tr R A /\ Irr R A.
  
Definition Con R A :=
  Rel R /\ 
  forall x y, x ∈ A /\ y ∈ A /\ x <> y -> 
  <|x,y|> ∈ R \/ <|y,x|> ∈ R.

Definition Tot R A :=
  Tr R A /\ Irr R A /\ Con R A.
  
Definition We R A :=
    Irr R A /\
    forall Y, Y ⊂ A /\ Y <> ∅ ->
    exists m, m ∈ Y /\ 
    forall y, y ∈ Y /\ y <> m -> <|m,y|> ∈ R /\ ~ <|y,m|> ∈ R.



Definition sim  f W1 W2 :=
  exists x1 x2 r1 r2, 
  M x1 /\ M x2 /\ M r1 /\ M r2 /\
  Rel r1 /\ Rel r2 /\ W1 = <|r1,x1|> /\ W2 = <|r2,x2|> /\
  Rel f /\ Un₁ f /\ Dom f = x1 /\ Ran f = x2 /\
  forall u v, u ∈ x1 /\ v ∈ x1 -> <|u,v|> ∈ r1 <-> <|Value f u , Value f v|> ∈ r2.

Definition Sim W1 W2 := exists Z, sim Z W1 W2.


Definition Fld R :=
  Dom R ∪ (Ran R).

  
Definition TOR R :=
  Rel R /\ Tot R (Fld R).

  
Definition WOR R :=
  Rel R /\ We R (Fld R).








Theorem we_con {R A} :
We R A -> Con R A.
Proof.
  move => [[RelR IrrRA] H].
  split => // x y [xA [yA _xy]].
  pose U := Pair x y.
  have _U : U <> ∅.
    rewrite not_empty.
    exists x; rewrite in_pair => //.
    by left.
    by is_set.
  have UA : U ⊂ A.
    move => u uU.
    apply in_pair in uU.
    case uU; move =>  -> //.
    is_set.
  move : (H U (conj UA _U)) => [m [mU Hm]].
  have m_ : M m by is_set.
  case /(in_pair x y m m_) : mU => [mx|my]; [left|right].
  + subst x.
    apply Hm.
    split; auto.
    apply in_pair => //.
     is_set.
     by right.
  + subst y.
    apply Hm.
    split; auto.
    apply in_pair => //.
     is_set.
     by left.
Qed.     
        

Theorem we_tr {R A} : 
  We R A -> Tr R A.
Proof.
  move => [[RelR IrrRA] H].
  split => // x y z [xA [yA [zA [xy_R yz_R]]]].
  pose U := (Single x) ∪ (Single y) ∪ (Single z).
  have UA : U ⊂ A.
    move => u uU.
    have u_ : M u by is_set.
    case /in_cup : uU => [uxy| uz].
      case /in_cup : uxy; rewrite in_single => // -> //.
      move /(in_single z u u_) : uz => // -> //.
  have _U : U <> ∅.
    rewrite not_empty.
    exists z.
    apply in_cup.
    right.
    apply in_single => //.
    is_set.
  move : (H U (conj UA _U)) => [m [mU Hm]].
  have m_ : M m by is_set.
  have xU : x ∈ U.
    apply in_cup; left; apply in_cup; left.
    apply in_single => //; is_set.
  have yU : y ∈ U.
    apply in_cup; left; apply in_cup; right.
    apply in_single => //; is_set.
  have zU : z ∈ U.
    apply in_cup; right.
    apply in_single => //; is_set.    
  move /in_cup : mU => [mxy |mz].
  + move /in_cup : mxy => [mx|my].
    - move /(in_single x m m_) : mx => mx; subst x.
      apply Hm; split => //.
      move => F.
      move : yz_R; subst z.
      apply Hm; split => //.
      move => F.
      move : xy_R; subst y.
      apply IrrRA => //.
    - move /(in_single y m m_) : my => my.
      case (classic (x = y)) => [zy | _zy].
      * subst y x => //.
      * subst y.
        move : (Hm x (conj xU _zy)) => [_ F].
        case (F xy_R).
  + move /(in_single z m m_) : mz => ma; subst z.
    case (classic (y = m)) => [ym | _ym].
    - subst y.
      case ((IrrRA m yA yz_R)).
    - apply NNPP => F.
      by move : yz_R; apply Hm.
Qed.      


Theorem we_tot R A : 
  We R A -> Tot R A.
Proof.
  intro.
  split.
  + apply (we_tr H).
  + split.
    apply H.
    apply (we_con H).
Qed.



Theorem sub_trans X Y Z :
    X ⊂ Y -> Y ⊂ Z -> X ⊂ Z.
Proof.
  intros XY YZ i Xi.
  apply (YZ i (XY i Xi)).
Qed.  


Theorem we_sub R X Y :
  We R X -> Y ⊂ X -> We R Y.
Proof.
  intros [[RelR IrrRA] we] YX.
  split => //.
  + split => //.
    move => x xY; apply IrrRA; apply YX => //.
  + move => Z [ZY _Z].
    apply we.
    split => //.
    by apply sub_trans with (Y := Y).
Qed.    


Theorem inverse_sim f X Y :
    sim f X Y -> sim (Inverse f) Y X.
Proof.
  move => [x1 [x2 [r1 [r2 [x1_ [x2_ [r1_ [r2_ 
           [Relr1 [Relr2 [X_r1x1 [Y_r2x2 
           [Relf [[unf unf'] [domf_x1 [ranf_x2 H]]]]]]]]]]]]]]]].
  exists x2; exists x1; exists r2; exists r1.
  split => //; split => //; split => //; split => //.
  split => //; split => //; split => //; split => //.
  split.
  move => p pf.
  move /in_inv : pf => [x [y [x_ [y_ [p_xy yx_f]]]]].
  apply in_prod.
  by exists x; exists y; rewrite !in_universe.
  split.
  split => //.
  rewrite inv_inv => //.
  split.
  rewrite dom_inverse => //.
  split.
  rewrite ran_inverse => //.
  move => u v [ux2 vx2].
  rewrite -ranf_x2 in ux2.
  rewrite -ranf_x2 in vx2.
  have u_ : M u by is_set.
  have v_ : M v by is_set.
  move /(in_ran f u u_) : ux2 => [s [s_ su_f]].
  move /(in_ran f v v_) : vx2 => [t [t_ tv_f]] .
  have st_x1 : s ∈ x1 /\ t ∈ x1.
    by rewrite -domf_x1 !in_dom => //; split; [exists u|exists v].
  move : (H s t st_x1) => {H} => H.
  case st_x1 => [sx1 tx1].
  rewrite -domf_x1 in sx1.
  rewrite -domf_x1 in tx1.
  move /(in_value f s u u_ unf sx1) : su_f => u_fs.
  move /(in_value f t v v_ unf tx1) : tv_f => v_ft.
  rewrite -u_fs in H; rewrite -v_ft in H.
  rewrite -H.
  rewrite u_fs v_ft.
  rewrite -!value_inv_value => //.
Qed.




Theorem sim_set {f X Y} :
    sim f X Y -> M f /\ M X /\ M Y.
Proof.
  move => [x1 [x2 [r1 [r2 [x1_ [x2_ [r1_ [r2_ 
           [Relr1 [Relr2 [X_r1x1 [Y_r2x2 
           [Relf [[unf unf'] [domf_x1 [ranf_x2 H]]]]]]]]]]]]]]]].

  split.  
  + apply sub_set with (y := x1 × x2).
    - apply product_set => //.
    - move => p pf.
      move : (Relf p pf) => pV.
      move /in_prod : pV => [x [y [x_ [y_ [p_xy _]]]]] ; subst p.
      apply in_prod.
      exists x; exists y.
      split => //; split => //; split => //.
      rewrite -domf_x1 -ranf_x2; split; [rewrite in_dom|rewrite in_ran] => //.
      by exists y.
      by exists x.
  + rewrite X_r1x1 Y_r2x2.
    split; apply orderd_set => //.
Qed.    


Theorem sim_comm X Y :
  Sim X Y -> Sim Y X.
Proof.
  intro.  
  induction H as [f].
  exists (Inverse f).
  by apply inverse_sim.
Qed.


Theorem sim_trans X Y U :
  Sim X Y -> Sim Y U -> Sim X U.
Proof.
  move => [f [x1 [x2 [r1 [r2 [x1_ [x2_ [r1_ [r2_ 
           [Relr1 [Relr2 [X_r1x1 [Y_r2x2 
           [Relf [[unf unf'] [domf_x1 [ranf_x2 Hf]]]]]]]]]]]]]]]]]

           [g [y1 [y2 [s1 [s2 [y1_ [y2_ [s1_ [s2_ 
           [Rels1 [Rels2 [X_s1y1 [W_s2y2 
           [Relg [[ung ung'] [domg_y1 [rang_y2 Hg]]]]]]]]]]]]]]]]].

  exists (g ○ f); exists x1; exists y2; exists r1; exists s2.
  split => //; split => //; split => //; split => //.
  split => //; split => //; split => //; split => //.
  
  have rsxy : r2 = s1 /\ x2 = y1.
    apply orderd_eq => //.
    by rewrite -Y_r2x2 X_s1y1.
  case rsxy => [l r]; subst x1 x2 y1 y2 r2.      

  split.
  move => p.
  rewrite in_compos in_prod.
  move => [x [y [z [x_ [y_ [z_ [p_xz [xy_f yz_g]]]]]]]].
  by exists x; exists z; rewrite !in_universe.

  split.
  split.
  apply un_composition => //.
  rewrite inv_compos.
  apply un_composition => //.

  split.
  equal => i.
  split => [H|H]; have i_ : M i by is_set.
    move /(in_dom _ i i_) : H => [y [y_ iy_gf]].
    move /(orderd_in_compos g f i y i_ y_) : iy_gf => [j [hj_ [ij_f jy_g]]].
    apply in_dom => //; exists j => //.

    move /(in_dom f i i_) : H => [j [j_ ij_f]].
    have j_ranf : j ∈ Ran f.
      apply in_ran => //.
      exists i => //.
    rewrite r in j_ranf.
    move /(in_dom g j j_) : j_ranf => [k [k_ jk_g]].
    apply in_dom => //.
    exists k; split => //.
    apply orderd_in_compos => //.
    exists j => //.
  
  split.
  equal => k.
  split => [H|H]; have k_ : M k by is_set.
      move /(in_ran _ k k_) : H=> [i [i_ ik_gf]].
      move /(orderd_in_compos g f i k i_ k_) : ik_gf => [j [j_ [ij_f jk_g]]].
      apply in_ran => //; exists j => //.

      move /(in_ran g k k_) : H => [j [j_ jk_g]].
      have j_domg : j ∈ Dom g.
        apply in_dom => //; exists k => //.
      rewrite -r in j_domg.
      move /(in_ran f j j_) : j_domg => [i [i_ ij_f]].
      apply in_ran => //; exists i; split  => //.
      apply /(orderd_in_compos g f i k i_ k_) => //; exists j => //.
    
  move => u v [u_domf v_domf].
  move : (Hf u v (conj u_domf v_domf)) => {Hf}  => Hf.
  have u_ : M u by is_set.
  have v_ : M v by is_set.
  have u_dom : u ∈ Dom f by done.
  have v_dom : v ∈Dom f by done.
  move /(in_dom f u u_) : u_domf => [p [p_ up_f]].
  move /(in_dom f v v_) : v_domf => [q [q_ vq_f]].
  have p_dom : p ∈ Dom g.
    rewrite -r; apply in_ran => //; exists u => //.
  have q_dom : q ∈ Dom g.
    rewrite -r; apply in_ran => //; exists v => //.            
  move /(in_value f u p p_ unf u_dom) : up_f => p_fu.
  move /(in_value f v q q_ unf v_dom) : vq_f => q_fv.
  rewrite Hf -p_fu -q_fv.
  move : (Hg p q (conj p_dom q_dom)) ->.
  have compos_value : forall a, a ∈ Dom f -> (g ○ f)[a] = g[f[a]].
    move => a a_dom.
    have a_ : M a by is_set.
    move /(in_dom f a a_) : a_dom => [b [b_ ab_f]].
    have b_dom : b ∈ Dom g.
      rewrite -r; apply in_ran => //.
      exists a => //.
    move /(in_dom g b b_) : b_dom => [c [c_ bc_g]].
    symmetry.
    apply in_value with (f := g ○ f).
    apply value_set.
    apply in_dom => //.
    apply value_set.
    apply in_dom => //; exists b => //.
    exists c; split => //.
    apply in_value in ab_f => //.
    by rewrite ab_f in bc_g.
    apply in_dom => //; exists b => //.
    apply un_composition => //.
    apply in_dom => //.
    exists c; split => //.
    apply orderd_in_compos => //.
    exists b => //.
    apply orderd_in_compos => //.
    apply value_set.
    apply in_dom => //.
    apply value_set => //.
    apply in_dom => //; exists b => //.
    exists c => //.
    apply in_value in ab_f => //.
    by rewrite ab_f in bc_g.
    apply in_dom => //; exists b => //.
    exists b; split => //; split => //.
    suff c_fga : c = g[f[a]].
      by rewrite -c_fga.
    apply in_value in ab_f => //.
    apply in_value in bc_g => //.
    by rewrite ab_f in bc_g.
    apply in_dom => //; exists c => //.
    apply in_dom => //; exists b => //.
  rewrite (compos_value u u_dom).
  rewrite (compos_value v v_dom).
  by rewrite p_fu q_fv.
Qed.  




  





Lemma ran_ex_value f x (x_ : M x) (unf : Un f):
  x ∈ Ran f -> exists y, x = f[y].
Proof.
  move /(in_ran f x x_) => [y [y_ yx_f]].
  exists y.
  apply in_value => //.
  apply in_dom => //.
  by exists x.
Qed.

Lemma dom_ex_value f x (x_ : M x) (unf : Un f):
  x ∈ Dom f -> exists y, y = f[x].
Proof.
  move /(in_dom f x x_) => [y [y_ xy_f]].
  exists y.
  apply in_value => //.
  apply in_dom => //.
  by exists y.
Qed. 



Lemma fld_set X (X_ : M X) :
  M (Fld X).
Proof.
  apply cup_set.
  apply dom_set => //.
  apply ran_set => //.
Qed.







Theorem sim_tor R G (R_ : M R) (G_ : M G) :
  Sim <|R, Fld R|>  <|G, Fld G|> -> TOR R -> TOR G.
Proof.
  move => [f [x1 [x2 [r1 [r2 [x1_ [x2_ [r1_ [r2_ 
  [Relr1 [Relr2 [R_r1x1 [G_r2x2 
  [Relf [[unf unf'] [domf_x1 [ranf_x2 Hf]]]]]]]]]]]]]]]]]
  [_ [[_ tr] [[_ irr] [_ conn]]]].
  move : (fld_set R R_) => fldR_.
  move : (fld_set G G_) => fldG_.  
  move /(orderd_eq _ _ _ _ R_ fldR_ r1_ x1_) : R_r1x1 => [a H1]; subst r1 x1.
  move /(orderd_eq _ _ _ _ G_ fldG_ r2_ x2_) : G_r2x2 => [a H2]; subst r2 x2.  
  split => //.
  split.
  + split => //; rewrite H2 => x y z [x_ranf [y_ranf [z_ranf [xy_G yz_G]]]].
    have x_ : M x by is_set.
    have y_ : M y by is_set.
    have z_ : M z by is_set.
    move /(in_ran f x x_) : x_ranf => [p [p_ px_f]].
    move /(in_ran f y y_) : y_ranf => [q [q_ qy_f]].
    move /(in_ran f z z_) : z_ranf => [r [r_ rz_f]].
    have p_domf : p ∈ Dom f. apply in_dom => //; exists x => //.
    have q_domf : q ∈ Dom f. apply in_dom => //; exists y => //.
    have r_domf : r ∈ Dom f. apply in_dom => //; exists z => //.
    have x_fp : x = f[p] by apply in_value.
    have y_fq : y = f[q] by apply in_value.
    have z_fr : z = f[r] by apply in_value.
    subst x y z.
    move /(Hf p q (conj p_domf q_domf)) : xy_G => pq_R.
    move /(Hf q r (conj q_domf r_domf)) : yz_G => qr_R.
    have _pq : p <> q.
      move => pq; subst p.
      move : pq_R; apply irr.
      by rewrite H1.
    have _qr : q <> r.
      move => qr; subst q.
      move : qr_R; apply irr.
      by rewrite H1.
    apply Hf => //.
    rewrite -H1 in p_domf; rewrite -H1 in q_domf; rewrite -H1 in r_domf.
    have _pr : p <> r.
      move => pr; subst r.
      have ppR : <|p,p|> ∈ R by apply tr with (y := q) => //.
      move : ppR; apply irr => //.
    
    move : (conn p q (conj p_domf (conj q_domf _pq))) => Hpq.
    move : (conn q r (conj q_domf (conj r_domf _qr))) => Hqr.
    case Hpq => [pqR|qpR].
    - case Hqr => [qrR|rqR].
      * apply tr with (y := q) => //.
      * have qqR : <|q,q|> ∈ R by apply tr with (y := r) => //.
        case (irr q q_domf qqR).
    - have ppR : <|p,p|> ∈ R by apply tr with (y := q) => //.
      case (irr p p_domf ppR).
  + split.
    - split => // x x_ranf xxG.
      rewrite H2 in x_ranf.
      have x_ : M x by is_set.
      move /(in_ran f x x_) : x_ranf => [p [p_ px_f]].
      have p_domf : p ∈ Dom f. apply in_dom => //; exists x => //.
      move /(in_value f p x x_ unf p_domf) : px_f => x_fp.
      rewrite x_fp in xxG.
      move /(Hf p p (conj p_domf p_domf)) : xxG.
      apply irr => //.
      by rewrite H1.
    - split => // x y.
      rewrite H2.
      move => [x_ranf [y_ranf _xy]].
      have x_ : M x by is_set.
      have y_ : M y by is_set.
      move /(in_ran f x x_) : x_ranf => [p [p_ px_f]].
      move /(in_ran f y y_) : y_ranf => [q [q_ qy_f]].
      have p_domf : p ∈ Dom f. apply in_dom => //; exists x => //.
      have q_domf : q ∈ Dom f. apply in_dom => //; exists y => //.
      have x_fp : x = f[p] by apply in_value.
      have y_fq : y = f[q] by apply in_value.
      subst x y.
      rewrite -(Hf p q (conj p_domf q_domf)).
      rewrite -(Hf q p (conj q_domf p_domf)).
      apply conn.
      rewrite H1.
      split => //; split => //.
      move => pq.
      apply _xy.
      by rewrite pq.
Qed.


Theorem sim_wor R G (R_ : M R) (G_ : M G) :
  Sim <|R, Fld R|>  <|G, Fld G|> -> WOR R -> WOR G.
Proof.
  move => [f [x1 [x2 [r1 [r2 [x1_ [x2_ [r1_ [r2_ 
  [Relr1 [Relr2 [R_r1x1 [G_r2x2 
  [Relf [[unf unf'] [domf_x1 [ranf_x2 Hf]]]]]]]]]]]]]]]]] 
  [_ [[_ irr] we]].
  move : (fld_set R R_) => fldR_.
  move : (fld_set G G_) => fldG_.  
  move /(orderd_eq _ _ _ _ R_ fldR_ r1_ x1_) : R_r1x1 => [a H1]; subst r1 x1.
  move /(orderd_eq _ _ _ _ G_ fldG_ r2_ x2_) : G_r2x2 => [a H2]; subst r2 x2.  
  split => //.
  split.
  + split => // x x_ranf xxG.
    rewrite H2 in x_ranf.
    have x_ : M x by is_set.
    move /(in_ran f x x_) : x_ranf => [p [p_ px_f]].
    have p_domf : p ∈ Dom f. apply in_dom => //; exists x => //.
    move /(in_value f p x x_ unf p_domf) : px_f => x_fp.
    rewrite x_fp in xxG.
    move /(Hf p p (conj p_domf p_domf)) : xxG.
    apply irr => //.
    by rewrite H1.
  + rewrite H2.
    move => Y [Y_ranf _Y].
    move /(not_empty) : _Y => [y yY].
    move : (Y_ranf y yY) => y_ranf.
    have y_ : M y by is_set.
    move /(in_ran f y y_) : y_ranf => [x [x_ xy_f]].
    pose Z := Image (Inverse f) Y.
    have ZY : Z ⊂ (Fld R).
      move => i Zi.
      have i_ : M i by is_set.
      move /(in_image _ Y i i_) : Zi => [j [j_ [jY ji_f]]].
      move /(@orderd_in_inv f j i j_ i_) in ji_f.
      rewrite H1.
      apply in_dom => //.
      by exists j.
    have _Z : Z <> ∅.
      apply not_empty.
      exists x.
      apply in_image => //.
      exists y.
      split => //; split => //.
      by apply (@orderd_in_inv f y x y_ x_).
    move : (we Z (conj ZY _Z)) => [m [mZ Hm]].
    have m_ : M m by is_set.
    move /(in_image _ Y m m_) : mZ => [n [n_ [nY nm_f']]].
    exists n; split => // b [bY _bn].
    move : (Y_ranf b bY) => l_ranf.
    have b_ : M b by is_set.
    move /(in_ran f b b_) : l_ranf => [a [a_ ab_f]].
    have a_domf : a ∈ Dom f by (apply in_dom => //; exists b => //).
    move /(in_value f a b b_ unf a_domf) : ab_f => b_fa.
    move /(@orderd_in_inv f n m n_ m_) : nm_f' => mn_f.
    have m_domf : m ∈ Dom f by (apply in_dom => //; exists n => //).
    move /(in_value f m n n_ unf m_domf) : mn_f => n_fm.
    rewrite b_fa n_fm.
    rewrite -(Hf m a (conj m_domf a_domf)).
    rewrite -(Hf a m (conj a_domf m_domf)).
    apply Hm.
    split.
    apply in_image => //.
    exists b. split => //; split => //.
    apply (@orderd_in_inv f b a) => //.
    apply in_value => //.
    by move => am; apply _bn; rewrite b_fa n_fm am.
Qed.   


Theorem we_ind X R (P : Class -> Prop) (weX : We R X) :
  (forall a, a ∈ X -> (forall b, b ∈ X -> <|b,a|> ∈ R -> P b) -> P a) -> forall a, a ∈ X -> P a.
Proof.
  move => H a aX.
  move : (we_tot R X weX) => [[RelE TrX] [[_ irrX] [_ conX]]].
  move : weX => [_ wex].
  apply NNPP => _Pa.
  pose Y := {:X | fun x => ~ P x:}.
  have aY : a ∈ Y by apply in_sep.
  have a_ : M a by is_set.
  have _Y : Y <> ∅.
    move => _Y.
    rewrite _Y in aY.  
    by move : (notin_empty a a_ aY).
  have YX : Y ⊂ X by apply sep_sub.
  move : (wex Y (conj YX _Y)) => [m [mY Hm]].
  move : (Hm a) => Ha.
  have we' : forall b, <|b,m|> ∈ R -> ~ b ∈ Y.
    move => b bm bY.
    case (classic (b = m)) => H0.
      subst m.
      move : bm; apply irrX.
      by move /in_sep : bY => [bX _].
      by move : (Hm b (conj bY H0)) => [_ F].
  case (classic (a = m)) => _ma.
  + subst m.
    move : (H a aX) => H0.
    case /imply_to_or : H0 => H1 => //.
    move /not_all_ex_not : H1 => [b Hb].
    move /(imply_to_and (b ∈ X) _) : Hb => [bX Hb].
    move /(imply_to_and _ (P b)) : Hb => [ba _Pb].
    apply (we' b ba).
    apply in_sep => //.
  + move : (Ha (conj aY _ma)) => [ma _am].
    move /in_sep : mY => [mX _Pm].
    apply _Pm.
    apply H => //.
    move => b bX bm.
    move : (we' b bm) => _bY.
    apply NNPP => _Pb.
    apply _bY.
    apply in_sep; split => //.
Qed.    






