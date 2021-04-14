Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Type_Safety
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.

Lemma tpre_refl: forall A,
  tpre A A.
Proof.
   inductions A; eauto.
Qed.


Lemma sim_refl: forall A,
 sim A A.
Proof.
  introv.
  inductions A; eauto.
Qed.

Lemma epre_lc: forall e1 e2,
 epre e1 e2 ->
 lc_exp e1 ->
 lc_exp e2.
Proof.
  introv ep lc. gen e2.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
Qed.

Lemma epre_lc2: forall e1 e2,
 epre e1 e2 ->
 lc_exp e2 ->
 lc_exp e1.
Proof.
  introv ep lc. gen e1.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
Qed.


Lemma epre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 epre u1 u2 ->
 lc_exp u1 ->
 lc_exp u2 ->
 epre [x~> u1]e1 [x~>u2]e2 .
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  - inductions H; simpl; eauto.
    + destruct (x == x0); eauto.
    + 
      apply ep_abs with (L := (singleton x)); intros; auto.
      forwards*: H0 x0 ep2 x.
      rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
      apply tpre_refl. apply tpre_refl.
    + apply ep_anno; eauto.
      apply tpre_refl.
    + apply ep_save; eauto.
      apply tpre_refl.
  - 
    apply ep_abs with (L := (union L (singleton x))); intros; auto.
    forwards*: H0 x0 ep2 x.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
Qed. 


Lemma Typing_c_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  Typing ((x , T1) :: E) (open_exp_wrt_exp e (e_var_f x)) Inf T2 ->
  Typing ((y , T1) :: E) (open_exp_wrt_exp e (e_var_f y)) Inf T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  Case "x = y".
    subst; eauto.
  Case "x <> y".
    assert (J : uniq (((x , T1) :: E))).
      eapply Typing_regular_2; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ ((y , T1) :: E)).
    apply Typing_subst_1 with (S := T1).
    simpl_env.
    SCase "(open x s) is well-typed".
      apply Typing_weaken. eauto. auto.
    SCase "y is well-typed". eauto.
Qed.

Theorem precise_type: forall e e' T T',
   epre e e' ->  
   Typing nil e Inf T ->
   Typing nil e' Inf T'->
   tpre T T'.
Proof.
    introv ep Typ1 Typ2.
    gen T T'.
    inductions ep; intros;
    try solve[inverts* Typ1; inverts* Typ2].
    - forwards*: inference_unique Typ1 Typ2. subst.
      apply tpre_refl.
    - inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep1 H2 H4.
      inverts* H.
Qed.


Lemma vval_pre: forall e1 e2,
  epre e1 e2 ->
  vvalue e1 ->
  vvalue e2.
Proof.
  introv ep vval1. gen e2.
  inductions vval1; intros; eauto.
  - inverts ep. eauto. inverts H3. eauto.
  - inverts ep. eauto. inverts* H4. 
    assert (epre (e_abs A e B) (e_abs A2 e2 B2)).
    eauto. 
    forwards*: epre_lc H0.
Qed.

Lemma val_pre: forall e1 e2,
  epre e1 e2 ->
  value e2 ->
  value e1.
Proof.
  introv ep vval1. gen e1.
  inductions vval1; intros; eauto.
  - inverts ep. eauto. inverts H3. eauto. 
  - inverts ep. eauto. inverts* H4.
    pick fresh x.
    forwards*: H6.
    assert(epre ((e_abs A1 e1 B1)) ((e_abs A e B))). eauto. 
    forwards*: epre_lc2 H1. 
  - inverts ep. inverts* H. inverts H; inverts* H4.
    assert(epre ((e_abs A2 e2 B1)) ((e_abs A1 e1 B))). eauto. 
    forwards*: epre_lc2 H. 
Qed.

Lemma val_prel: forall e1 e2,
  epre e1 e2 ->
  value e1 ->
  value e2.
Proof.
  introv ep vval1. gen e2.
  inductions vval1; intros; eauto.
  - inverts ep. eauto. inverts H3. eauto. 
  - inverts ep. eauto. inverts* H4.  
    assert(epre ((e_abs A e B)) ((e_abs A2 e2 B2))). eauto. 
    forwards*: epre_lc H0.
  - inverts ep. inverts* H. inverts* H. inverts* H4. 
     assert(epre ((e_abs A0 e1 B0)) ((e_abs A2 e3 B2))). eauto. 
    forwards*: epre_lc H.
    inverts* H4.  
Qed.

Lemma epre_sim : forall A1 B1 A2 B2,
  sim A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  sim A2 B2.
Proof.
  introv s1 tp1 tp2. gen A2 B2.
  inductions s1; intros; eauto.
  - inverts tp1. inverts* tp2. inverts* tp2.
  - inverts* tp1.
    inverts* tp2.
  - inverts* tp1.
  - inverts* tp2. 
Qed.


Lemma tdynamic_guarantee: forall e1 e2 e1' A B,
 epre e1 e2 ->  
 tpre A B ->
 value e1 ->
 Typing nil e1 Chk A ->
 Typing nil e2 Chk B -> 
 cTypedReduce e1 A (Expr e1') ->
 exists e2', cTypedReduce e2 B (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep tp val typ1 typ2 red. gen e2 B .
  inductions red; intros; eauto.
  - forwards*: val_prel ep. 
    inverts val.
    + destruct B.
      * inverts tp. inverts ep. inverts typ2. inverts H3.
        inverts H7. inverts H3. inverts H4.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto. inverts H6.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto. inverts ep.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto. inverts H6.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
      * inverts* H0.
      * inverts tp. inverts typ2.
        inverts ep.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto. inverts H8.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
    + destruct B.
      * inverts tp. inverts ep. inverts typ2. inverts H4.
        inverts H8. inverts H4. inverts H6. inverts H5.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
        inverts H7.  inverts typ2. inverts H4.
        inverts H9. inverts H4. inverts H7. inverts H6. inverts H0.
        inverts H0. inverts H0.
      * inverts tp. inverts ep.  inverts typ2. inverts H4.
         exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
        forwards*: value_lc H1. inverts H2.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
        inverts ep.
        simpl in H0. 
        assert(tpre (t_arrow A0 B1) (t_arrow A0 B1)). apply tpre_refl.
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H0 H4 H6.
        exists. split.
        apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
        inverts H9.
        simpl in H0. 
        assert(tpre (t_arrow A0 B1) (t_arrow A0 B1)). apply tpre_refl.
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H0 H4 H8.
        exists. split.
        apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
        simpl in H0. 
        assert(tpre (t_arrow A0 B1) (t_arrow A2 B4)). eauto. 
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H0 H2 H4.
        exists. split. 
        assert (epre (e_abs A0 e0 B1) (e_abs A2 e2 B4)).
        eauto. forwards*: epre_lc H9.
        apply ep_anno; eauto.
      * inverts tp. inverts typ2.
        inverts ep.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
        forwards*: value_lc H1. inverts H5.
        exists. split. apply cTReduce_sim; eauto.
        apply ep_anno; eauto.
  - inverts* ep. inverts typ2. inverts H1.
    + destruct B.
      * inverts tp.
       exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto. inverts* H0.
        exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto. inverts* H0.
      * inverts tp.
         exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto. inverts* H0.
        inverts H6.
        simpl in H. 
        assert(tpre (t_arrow A B) (t_arrow A B)). apply tpre_refl. 
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H H3 H6.
        exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto.  inverts H.
      * inverts tp.
        exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto. inverts* H0.
    + destruct B.
      * inverts val. inverts tp. inverts H1. inverts H.
        inverts H4.  exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto.  inverts H1. inverts H.
        exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto.
      * inverts tp.
         exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto. inverts val. inverts H1. 
        inverts H4. 
        simpl in H. 
        assert(tpre (t_arrow A0 B) (t_arrow A0 B)). apply tpre_refl. 
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H H4 H5.
        exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto.
        assert(tpre (t_arrow A0 B) (t_arrow A2 B4)). eauto. 
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H H1 H4.
        assert (epre (e_abs A0 e1 B) (e_abs A2 e3 B4)). 
        eauto. forwards*: epre_lc H7.
        inverts H.
      * inverts tp.
        exists. split. apply cTReduce_savep; eauto.
        apply ep_anno; eauto. 
Qed.

Lemma dynamic_guarantee_dir: forall e1 e2 e1' dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 -> 
 cstep e1 (Expr e1') ->
 exists e2', cstep e2 (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red. gen e1' dir T1 T2.
  inductions ep; intros; eauto.
  - exists. split. apply red. apply ep_refl.
    forwards*: cpreservation typ1. 
    forwards*: Typing_regular_1 H0.
  - inverts red. exists. split. assert (epre (e_abs A1 e1 B1) (e_abs A2 e2 B2)).
    eauto. forwards*: epre_lc H3. apply ep_anno; eauto.
    destruct E; unfold simpl_fill in H3; inverts* H3. 
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      inverts typ1. inverts typ2. 
      forwards*: IHep1 H2. inverts H. inverts H0.
      exists. rewrite sfill_appl. split. apply cdo_step; eauto.
      unfold simpl_fill. eauto.
      inverts typ2. inverts H. inverts H3. 
      forwards*: IHep1 H2. inverts H. inverts H3.
      exists. rewrite sfill_appl. split. apply cdo_step; eauto.
      unfold simpl_fill. eauto.
      inverts typ1.  inverts typ2. 
      forwards*: IHep2 H2. inverts H. inverts H0.
      rewrite sfill_appr. exists. inverts H1.  split.
      apply cdo_step; eauto. forwards*: vval_pre ep1. unfold simpl_fill. eauto.
      inverts typ2.  inverts H. inverts H3. 
      forwards*: IHep2 H2. inverts H. inverts H3.
      rewrite sfill_appr. exists. inverts H1.  split.
      apply cdo_step; eauto. forwards*: vval_pre ep1. unfold simpl_fill. eauto.
    + inverts* ep1.
      forwards*: vval_pre ep2.
      exists. split. apply cStep_beta; eauto.
      apply ep_anno; eauto. apply tpre_refl.
      apply ep_anno; eauto. apply tpre_refl.
      forwards*: vval_val H3.
      forwards*: vval_val H0.

      assert (epre (e_anno (e_anno e2 A2) A1) (e_anno (e_anno e2' A2) A1)).
      apply ep_anno; eauto. apply tpre_refl.
      apply ep_anno; eauto. apply tpre_refl. 
      pick fresh x.
      assert((e ^^ e_anno (e_anno e2' A2) A1) = [x ~> e_anno (e_anno e2' A2) A1] (e ^ x)).
      rewrite (subst_exp_intro x); eauto.
      rewrite (subst_exp_intro x); eauto.
      rewrite H6.
      forwards*: vval_val H3. forwards*: vval_val H0.
      forwards*: value_lc H7. forwards*: value_lc H8.
      assert(lc_exp (e_anno (e_anno e2 A2) A1)); eauto.
      assert(lc_exp (e_anno (e_anno e2' A2) A1)); eauto.
      inverts H2. forwards*: H14 x.
      assert(epre (e^x) (e^x)); eauto.
      forwards*: epre_open H13 H5 H11 H12.

      inverts* H5. inverts* H1.
      inverts typ2. inverts H5.
      inverts H0. inverts H7.
      forwards*: vval_pre ep2.
      exists. split. apply cStep_beta; eauto.
      apply ep_anno; eauto. 
      apply ep_anno; eauto. apply tpre_refl.
      assert (epre (e_anno (e_anno e2 A2) A1) (e_anno (e_anno e2' C) A1)).
      apply ep_anno; eauto. apply tpre_refl.
      pick fresh x.
      assert((e ^^ e_anno (e_anno e2' C) A1) = [x ~>e_anno (e_anno e2' C) A1] (e ^ x)).
      rewrite (subst_exp_intro x); eauto.
      rewrite (subst_exp_intro x); eauto.
      rewrite H4.
      forwards*: vval_val H3. forwards*: vval_val H0.
      forwards*: value_lc H6. forwards*: value_lc H8.
      assert(lc_exp (e_anno (e_anno e2 A2) A1)); eauto.
      assert(lc_exp (e_anno (e_anno e2' C) A1)); eauto.
      inverts H2. forwards*: H14 x.
      assert(epre (e^x) (e^x)); eauto.
      forwards*: epre_open H13 H1 H11 H12.

      inverts typ2. inverts H5.
      forwards*: vval_pre ep2.
      exists. split. apply cStep_beta; eauto. 
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)).
      eauto. forwards*: epre_lc H0.
      apply ep_anno; eauto. inverts H1. auto. 
      apply ep_anno; eauto. inverts H4.
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)).
      eauto.
      forwards*: epre_lc H4. 
      pick fresh x.
      forwards*: H6.
      assert(x `notin` (fv_exp e)). eauto.
      assert(x `notin` (fv_exp e3)). eauto.
      assert((e3 ^^ e_anno (e_anno e2' A) A3) = [x ~> e_anno (e_anno e2' A) A3] (e3 ^ x)).
      rewrite (subst_exp_intro x). eauto. auto.
      rewrite (subst_exp_intro x); eauto.
      forwards*:vval_val H3.
      forwards*:vval_val H.
      inverts typ1. inverts H20. inverts H23. inverts H17. inverts H18.
      inverts H0. inverts H5.
      assert (Typing nil (e_anno (e_anno e2 A4) A1) Inf A1).
      apply Typ_anno; eauto. eapply Typ_sim; eauto.
      apply BA_AB. auto.
      forwards*: value_no_fv H0.
      assert (Typing nil (e_anno (e_anno e2' A) A3) Inf A3).
      apply Typ_anno; eauto. eapply Typ_sim; eauto.
      apply BA_AB. auto.
      forwards*: value_no_fv H17.
      forwards*: value_lc H15. forwards*: value_lc H16.
      assert (lc_exp (e_anno (e_anno e2 A4) A1)). eauto.
      assert (lc_exp (e_anno (e_anno e2' A) A3)). eauto. inverts H1.
      assert (epre (e_anno (e_anno e2 A4) A1) (e_anno (e_anno e2' A) A3)).
      apply ep_anno; eauto. 
      rewrite H14.
      forwards*: epre_open H10 H1.
      
      inverts* H1. inverts* H. 
      inverts H7. inverts H. inverts H10.
      inverts H13. inverts H.
      forwards*: vval_pre ep2.
      exists. split. apply cStep_beta; eauto.
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)).
      eauto.
      forwards*: epre_lc H4. 
      pick fresh x.
      forwards*: H6.
      assert(x `notin` (fv_exp e)). eauto.
      assert(x `notin` (fv_exp e3)). eauto.
      assert((e3 ^^ e_anno (e_anno e2' A0) A3) = [x ~> e_anno (e_anno e2' A0) A3] (e3 ^ x)).
      rewrite (subst_exp_intro x). eauto. auto.
      rewrite (subst_exp_intro x); eauto.
      rewrite H13.
      forwards*: vval_val H3. forwards*: vval_val H.
      forwards*: value_lc H14. forwards*: value_lc H16.
      assert(lc_exp (e_anno (e_anno e2 A2) A1)); eauto.
      assert(lc_exp (e_anno (e_anno e2' A0) A3)); eauto.
      (* forwards*: H14 x. *)
      assert(epre (e^x) (e3^x)); eauto.
      apply ep_anno; eauto.
      apply ep_anno; eauto.
      forwards*: epre_open H21 H19 H20.
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      inverts typ1. inverts typ2. inverts H4. inverts H5. inverts H6. inverts H7.
      forwards*: IHep1 H2. inverts H7. inverts H10.
      exists. rewrite sfill_addl. split. apply cdo_step; eauto.
      unfold simpl_fill. eauto.
      inverts typ2. inverts H3. inverts H. 
      forwards*: IHep1 H2. inverts H. inverts H3.
      exists. rewrite sfill_addl. split. apply cdo_step; eauto.
      unfold simpl_fill. eauto.
      inverts typ1. inverts typ2. 
      forwards*: IHep2 H2. inverts H. inverts H0.
      exists. rewrite sfill_addr. split. apply cdo_step; eauto.
      inverts H1. forwards*: vval_pre ep1.
      unfold simpl_fill. eauto.
      inverts typ2. inverts H.  inverts H3. inverts H1.
      forwards*: IHep2 H2. inverts H . inverts H1.
      rewrite sfill_addr. exists.   split.
      apply cdo_step; eauto. forwards*: vval_pre ep1. unfold simpl_fill. eauto.
    + inverts typ2. inverts ep1. inverts ep2.
      exists. split. apply cStep_addb; eauto. eauto.
      inverts H6. exists. split. apply cStep_addb; eauto. eauto.
      inverts H4. inverts ep2.
      exists. split. apply cStep_addb; eauto. eauto.
      inverts H7. exists. split. apply cStep_addb; eauto. eauto.
      inverts H. inverts ep1. inverts ep2.
      exists. split. apply cStep_addb; eauto. eauto.
      inverts H7. exists. split. apply cStep_addb; eauto. eauto.
      inverts H6. inverts ep2.
      exists. split. apply cStep_addb; eauto. eauto.
      inverts H8. exists. split. apply cStep_addb; eauto. eauto.
  - inverts red.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    assert (not (value (e_anno e2 A))).
    unfold not; intros. assert (epre (e_anno e1 A) (e_anno e2 A)).
    apply ep_anno; eauto. apply tpre_refl.
    apply H4. forwards*: val_pre H1.
    inverts typ1.  inverts typ2. 
    forwards*: IHep H3. inverts H1. inverts H2.
    exists. split. apply cStep_anno; eauto. 
    unfold not; intro. inverts H2.
    apply H0. eauto. apply H0. eauto.
    apply ep_anno; eauto.
    inverts typ2. inverts H1.  inverts H5.
    forwards*: IHep H3. inverts H1. inverts H5.
    exists. split. apply cStep_anno; eauto. 
    unfold not; intro. inverts H5.
    apply H0. eauto. apply H0. eauto.
    apply ep_anno; eauto.
    inverts typ1. inverts typ2.
    forwards*: tdynamic_guarantee H7 H3 H4. inverts H0.
    inverts H1. exists. split. apply cStep_annov; eauto.
    forwards*: val_prel ep.  auto.
    inverts typ2. inverts H0.  inverts H3.
    forwards*: tdynamic_guarantee H8 H7 H4. inverts H0.
    inverts H3. exists. split. apply cStep_annov; eauto.
    forwards*: val_prel ep.  auto.
  - forwards*: cstep_not_value red. inverts typ1.
    eauto.
    forwards*: cstep_not_value red. inverts H0.
    eauto.
Qed.

Lemma dynamic_guarantee: forall e1 e2 e1' T1 T2,
 epre e1 e2 ->  
 Typing nil e1 Inf T1 ->
 Typing nil e2 Inf T2 -> 
 cstep e1 (Expr e1') ->
 exists e2', cstep e2 (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red. gen e1' T1 T2.
  inductions ep; intros; eauto.
  - exists. split. apply red. apply ep_refl.
    forwards*: cpreservation typ1. 
    forwards*: Typing_regular_1 H0.
  - inverts red. exists. split. assert (epre (e_abs A1 e1 B1) (e_abs A2 e2 B2)).
    eauto. forwards*: epre_lc H3. apply ep_anno; eauto.
    destruct E; unfold simpl_fill in H3; inverts* H3. 
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      inverts typ1. inverts typ2. 
      forwards*: IHep1 H2. inverts H. inverts H0.
      exists. rewrite sfill_appl. split. apply cdo_step; eauto.
      unfold simpl_fill. eauto.
      inverts typ1. inverts H5. inverts typ2. inverts H8.
      forwards*: IHep2 H2. inverts H6.
      rewrite sfill_appr. exists. inverts H1. inverts H8. split.
      apply cdo_step; eauto. forwards*: vval_pre ep1. unfold simpl_fill. eauto.
    + inverts* ep1.
      forwards*: vval_pre ep2.
      exists. split. apply cStep_beta; eauto.
      apply ep_anno; eauto. apply tpre_refl.
      apply ep_anno; eauto. apply tpre_refl.
      forwards*: vval_val H3.
      forwards*: vval_val H0.

      assert (epre (e_anno (e_anno e2 A2) A1) (e_anno (e_anno e2' A2) A1)).
      apply ep_anno; eauto. apply tpre_refl.
      apply ep_anno; eauto. apply tpre_refl. 
      pick fresh x.
      assert((e ^^ e_anno (e_anno e2' A2) A1) = [x ~> e_anno (e_anno e2' A2) A1] (e ^ x)).
      rewrite (subst_exp_intro x); eauto.
      rewrite (subst_exp_intro x); eauto.
      rewrite H6.
      forwards*: vval_val H3. forwards*: vval_val H0.
      forwards*: value_lc H7. forwards*: value_lc H8.
      assert(lc_exp (e_anno (e_anno e2 A2) A1)); eauto.
      assert(lc_exp (e_anno (e_anno e2' A2) A1)); eauto.
      inverts H2. forwards*: H14 x.
      assert(epre (e^x) (e^x)); eauto.
      forwards*: epre_open H13 H5 H11 H12.

      inverts* H5. inverts* H1.
      inverts typ2. inverts H5.
      forwards*: vval_pre ep2.
      exists. split. apply cStep_beta; eauto.
      apply ep_anno; eauto. 
      apply ep_anno; eauto. apply tpre_refl.
      assert (epre (e_anno (e_anno e2 A2) A1) (e_anno (e_anno e2' C) A1)).
      apply ep_anno; eauto. apply tpre_refl.
      pick fresh x.
      assert((e ^^ e_anno (e_anno e2' C) A1) = [x ~>e_anno (e_anno e2' C) A1] (e ^ x)).
      rewrite (subst_exp_intro x); eauto.
      rewrite (subst_exp_intro x); eauto.
      rewrite H4.
      forwards*: vval_val H3. forwards*: vval_val H0.
      forwards*: value_lc H6. forwards*: value_lc H8.
      assert(lc_exp (e_anno (e_anno e2 A2) A1)); eauto.
      assert(lc_exp (e_anno (e_anno e2' C) A1)); eauto.
      inverts H2. forwards*: H14 x.
      assert(epre (e^x) (e^x)); eauto.
      forwards*: epre_open H13 H1 H11 H12.

      inverts typ2. inverts H5.
      forwards*: vval_pre ep2.
      exists. split. apply cStep_beta; eauto. 
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)).
      eauto. forwards*: epre_lc H0.
      apply ep_anno; eauto. inverts H1. auto. 
      apply ep_anno; eauto. inverts H4.
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)).
      eauto.
      forwards*: epre_lc H4. inverts H10. inverts H2.
      pick fresh x.
      forwards*: H6.
      assert(x `notin` (fv_exp e)). eauto.
      assert(x `notin` (fv_exp e3)). eauto.
      assert((e3 ^^ e_anno (e_anno e2' A) A3) = [x ~> e_anno (e_anno e2' A) A3] (e3 ^ x)).
      rewrite (subst_exp_intro x). eauto. auto.
      rewrite (subst_exp_intro x); eauto.
      forwards*:vval_val H3.
      forwards*:vval_val H.
      inverts typ1. inverts H20. inverts H23. inverts H17. inverts H18.
      inverts H0. inverts H5.
      assert (Typing nil (e_anno (e_anno e2 A4) A1) Inf A1).
      apply Typ_anno; eauto. eapply Typ_sim; eauto.
      apply BA_AB. auto.
      forwards*: value_no_fv H0.
      assert (Typing nil (e_anno (e_anno e2' A) A3) Inf A3).
      apply Typ_anno; eauto. eapply Typ_sim; eauto.
      apply BA_AB. auto.
      forwards*: value_no_fv H17.
      forwards*: value_lc H15. forwards*: value_lc H16.
      assert (lc_exp (e_anno (e_anno e2 A4) A1)). eauto.
      assert (lc_exp (e_anno (e_anno e2' A) A3)). eauto. inverts H1.
      assert (epre (e_anno (e_anno e2 A4) A1) (e_anno (e_anno e2' A) A3)).
      apply ep_anno; eauto. 
      rewrite H14.
      forwards*: epre_open H2 H1 H28 H29. 
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      inverts typ1. inverts typ2. inverts H4. inverts H5. inverts H6. inverts H7.
      forwards*: IHep1 H2. inverts H7. inverts H10.
      exists. rewrite sfill_addl. split. apply cdo_step; eauto.
      unfold simpl_fill. eauto.
      inverts typ1. inverts H5.  inverts typ2. inverts H8.
      forwards*: IHep2 H2. inverts H6. inverts H8.
      rewrite sfill_addr. exists. inverts H1.  split.
      apply cdo_step; eauto. forwards*: vval_pre ep1. unfold simpl_fill. eauto.
    + inverts typ2. inverts ep1. inverts ep2.
      exists. split. apply cStep_addb; eauto. eauto.
      inverts H6. exists. split. apply cStep_addb; eauto. eauto.
      inverts H5. inverts ep2.
      exists. split. apply cStep_addb; eauto. eauto.
      inverts H7. exists. split. apply cStep_addb; eauto. eauto.
  - inverts red.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    assert (not (value (e_anno e2 A))).
    unfold not; intros. assert (epre (e_anno e1 A) (e_anno e2 A)).
    apply ep_anno; eauto. apply tpre_refl.
    apply H4. forwards*: val_pre H1.
    inverts typ1. inverts H5. inverts typ2. inverts H7.
    forwards*: IHep H3. inverts H7. inverts H8.
    exists. split. apply cStep_anno; eauto. 
    unfold not; intro. inverts H8.
    apply H0. eauto. apply H0. eauto.
    apply ep_anno; eauto. inverts typ1. inverts typ2.
    forwards*: tdynamic_guarantee H3 H5 H4. inverts H0.
    inverts H1. exists. split. apply cStep_annov; eauto.
    forwards*: val_prel ep.  auto.
  - forwards*: cstep_not_value red. inverts typ1.
    eauto.
Qed.

Lemma dynamic_guarantees: forall e1 e2 m1 T1 T2,
 epre e1 e2 ->  
 Typing nil e1 Inf T1 ->
 Typing nil e2 Inf T2 ->
 vvalue m1 ->
 e1 ->* (Expr m1) ->
 exists m2, vvalue m2 /\ e2 ->* (Expr m2) /\ epre m1 m2.
Proof.
  introv ep typ1 typ2 val red. gen e2 T1 T2 . 
  inductions red; intros.
  - forwards*: vval_pre ep.
  - forwards*: dynamic_guarantee ep typ1 typ2 H.
    inverts H0. inverts H1.
    forwards*: cpreservation H.
    forwards*: cpreservation H0.
    forwards*: IHred val H2 H1 H3.
    inverts H4. inverts H5. inverts H6.
    exists. split. apply H4. split.
    apply star_trans with (b := x).
    apply star_one. apply H0.
    apply H5. auto.
Qed.

Lemma dynamic_guarantees2: forall e1 e2 dir m1 T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 vvalue m1 ->
 e1 ->* (Expr m1) ->
 exists m2, vvalue m2 /\ e2 ->* (Expr m2) /\ epre m1 m2.
Proof.
  introv ep typ1 typ2 val red. gen e2 T1 dir T2 . 
  inductions red; intros.
  - forwards*: vval_pre ep.
  - forwards*: dynamic_guarantee_dir ep typ1 typ2 H.
    inverts H0. inverts H1.
    forwards*: cpreservation H.
    forwards*: cpreservation H0.
    forwards*: IHred val H2 H1 H3.
    inverts H4. inverts H5. inverts H6.
    exists. split. apply H4. split.
    apply star_trans with (b := x).
    apply star_one. apply H0.
    apply H5. auto.
Qed.
