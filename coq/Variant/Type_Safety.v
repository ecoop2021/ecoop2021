Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.

Lemma value_decidable: forall v,
   lc_exp v -> value v \/ not (value v).
Proof.
  introv lc. inductions v; eauto;
  try solve [right; unfold not; intros nt; inverts nt].
  - inverts lc. forwards*: IHv. inverts H.
    + inverts H1;try solve [right; unfold not; intros nt; inverts nt].
    + inductions v; eauto;
      try solve [right; unfold not; intros nt; inverts nt].
  - inverts lc. forwards*: IHv. inverts H.
    + inverts H1;try solve [right; unfold not; intros nt; inverts nt].
      right. unfold not;intros. inverts H. inverts H2.
      right. unfold not;intros. inverts H1. inverts H3.
      right. unfold not;intros. inverts H1. inverts H3.
    + inductions v; eauto;
      try solve [right; unfold not; intros nt; inverts nt; inverts H2].
Qed.



Lemma sim_decidable:forall A B,
sim A B \/ ~ (sim A B).
Proof.
  introv.
  gen A.
  inductions B; intros; eauto.
  - inductions A; eauto. right. unfold not;  intros. inverts* H.
  - inductions A; eauto. right. unfold not; intros.
    inverts* H.
    forwards*: IHB1 A1. forwards*: IHB2 A2.
    destruct H.  destruct H0. left.  eauto. right.
    unfold not; intros. inverts* H1. destruct H0.
    right. unfold not; intros. inverts* H1.
    right. unfold not; intros. inverts* H1.
Qed.

Lemma eq_type: forall A,
 (A = t_dyn) \/ ~(A = t_dyn).
Proof.
  introv.
  inductions A;
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros H; 
  inverts* H].
Qed.

Lemma TypedReduce_trans : forall v v1 v2 A B,
    value v -> TypedReduce v A (Expr v1) -> TypedReduce v1 B (Expr v2) -> TypedReduce v B (Expr v2).
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B v2.
  inductions Red1;
    introv Red2; eauto.
  - inverts* Red2. 
  - inverts* Red2.
  - inverts* Val.
    inverts* H1.
    inverts* Red2.
    inverts* Red2.
  - inverts* Red2.
Qed.

Lemma TypedReduce_prv_value: forall v A v',
    value v -> TypedReduce v A (Expr v') -> value v'.
Proof.
  intros v A v' Val Red.
  inductions Red; eauto.
  - inverts* Val.
  - eapply value_save.
    inverts Val.
    auto. eauto.
  - inverts* Val.
    inverts H1; inverts* H.
  - apply value_save.
    inverts* Val.
Qed.

Lemma principle_inf: forall v A,
  sval v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed. 


Lemma principle_inf2: forall v A,
  value v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed.

Lemma TypedReduce_preservation: forall v A v' B,
    value v -> TypedReduce v A (Expr v') -> Typing nil v Chk B -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  + inverts* Typ. inverts H1. inverts H5.
    eapply Typ_anno; eauto.
    inverts Val.
    forwards*: principle_inf H1.
    eapply Typ_sim; eauto.
    forwards*: principle_inf H1.
    rewrite H4 in H0. auto.
  + inverts* Typ.
    inverts* H1.
    eapply Typ_save; eauto.
    inverts Val. eauto. eauto.
    inverts H5.
    forwards*: principle_inf H1.
    inverts Val; eauto.
    rewrite H4. auto.
  + inverts* Val.
    inverts Typ. inverts H0.
    eapply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    forwards*: principle_inf H8.
    rewrite H0 in H. auto.
  + inverts* Typ.
    inverts* H0.
    eapply Typ_save; eauto.
    forwards*: principle_inf H7.
    rewrite H0 in H. auto.
Qed.

Lemma cTypedReduce_preservation: forall v A v' B,
    value v -> cTypedReduce v A (Expr v') -> Typing nil v Chk B -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  + inverts* Typ. inverts H1. inverts H5.
    eapply Typ_anno; eauto.
    inverts Val.
    forwards*: principle_inf H1.
    eapply Typ_sim; eauto.
    forwards*: principle_inf H1.
    rewrite H4 in H0. auto.
  + inverts* Val.
    inverts Typ. inverts H0.
    eapply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    forwards*: principle_inf H8.
    rewrite H0 in H. auto.
Qed.

Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.

Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (Expr e') ->
    Typing nil e' dir A.
Proof.
  introv Typ. gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; inverts* J]; introv J.
  - inverts J.
    apply Typ_anno; eauto.
    destruct E; unfold simpl_fill in H0; inverts H0.
  - inverts H0.
  - inverts* J.
    + eapply Typ_anno; eauto.
      eapply Typ_sim; eauto.
      apply sim_refl.
    + destruct E; unfold simpl_fill in H1; inverts H1.
  - Case "typing_app".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    + inverts Typ1.
      inverts* H5.
      inverts* H.
      pick fresh x.
      rewrite (subst_exp_intro x); eauto.
      forwards*: H8.
      inverts* H.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply typing_c_subst_simpl; eauto.
      eapply Typ_anno.
      inverts H0.
      eapply Typ_sim; eauto.
      eapply BA_AB. auto.
      auto.
      inverts H0.
      auto.
  - inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
  - Case "typing_anno".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
    + eapply TypedReduce_preservation; eauto.
  - inverts* J.
    destruct E; unfold simpl_fill in H2; inverts H2.
Qed.

Theorem cpreservation : forall e e' dir A,
    Typing nil e dir A ->
    cstep e (Expr e') ->
    Typing nil e' dir A.
Proof.
  introv Typ. gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; inverts* J]; introv J.
  - inverts J.
    apply Typ_anno; eauto.
    destruct E; unfold simpl_fill in H0; inverts H0.
  - inverts H0.
  - inverts* J.
    + eapply Typ_anno; eauto.
      eapply Typ_sim; eauto.
      apply sim_refl.
    + destruct E; unfold simpl_fill in H1; inverts H1.
  - Case "typing_app".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    + inverts Typ1.
      inverts* H5.
      inverts* H.
      pick fresh x.
      rewrite (subst_exp_intro x); eauto.
      forwards*: H8.
      inverts* H.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply typing_c_subst_simpl; eauto.
      eapply Typ_anno.
      inverts H0.
      eapply Typ_sim; eauto.
      eapply BA_AB. auto.
      auto.
      inverts H0.
      auto.
  - inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
  - Case "typing_anno".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
    + eapply cTypedReduce_preservation; eauto.
  - inverts* J.
    destruct E; unfold simpl_fill in H2; inverts H2.
Qed.

Lemma sfill_appl : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_appr : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addl : forall e1 e2,
  (e_add e1 e2) = (simpl_fill (saddCtxL e2) e1).
Proof.
  intros. eauto.
Qed.


Lemma sfill_addr : forall e1 e2,
  (e_add e1 e2) = (simpl_fill (saddCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma TypedReduce_progress: forall v A,
    value v -> Typing [] v Chk A -> exists r, TypedReduce v A r.
Proof.
  intros v A Val Typ. gen A.
  inductions Val; intros. 
  - inverts Typ. inverts H. inverts H3. 
    forwards*: principle_inf H.
    destruct (sim_decidable A  A0).
    rewrite <- H2 in H3.
    exists.
    apply TReduce_sim; eauto.  rewrite <- H2 in H3.
    exists.
    apply TReduce_simp; eauto.
  - inverts Typ. inverts H0. inverts H4. 
    forwards*: principle_inf H0.
    destruct (sim_decidable A2  A0).
    rewrite <- H3 in H4.
    exists.
    apply TReduce_sim; eauto.  
    rewrite <- H3 in H4.
    exists.
    apply TReduce_simp; eauto.
  - inverts Typ. inverts H0. 
    forwards*: principle_inf H7.
    destruct (sim_decidable B  A0).
    rewrite <- H0 in H2.
    exists.
    apply TReduce_savep; eauto.  
    rewrite <- H0 in H2.
    exists.
    apply TReduce_save; eauto.
Qed.

Lemma vval_dec: forall v,
  value v -> 
  (vvalue v) \/ ~(vvalue v).
Proof.
  introv val.
  inductions val; eauto.
  right. unfold not; intros.
  inverts* H0.
Qed.



Theorem progress : forall e dir T,
    Typing nil e dir T ->
    value e \/ (exists r, step e r).
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ; 
      lets Lc  : Typing_regular_1 Typ';
      try solve [left*];
      try solve [right*].
  - Case "var".
    inverts* H0.
  - right. inverts Lc. 
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    inverts* Typ1;
    try solve [ inverts Val1 ].
    + forwards*: vval_dec Val2. destruct H0.
      inverts H. inverts* Val1; inverts* H3; inverts H4.
      inverts* Val2; try solve [exfalso; apply H0; eauto].
      exists. rewrite sfill_appr. apply Step_save; eauto.
      apply swf_appr; eauto. inverts Val1. eauto. eauto.
    + exists.
      rewrite sfill_appl.
      apply Step_save; eauto.
    + forwards*: vval_dec Val1. destruct H.
      rewrite sfill_appr. destruct e2'.
      exists. apply do_step; eauto. exists. apply blame_step; eauto.
      inverts* Val1; try solve [exfalso; apply H; eauto].
      rewrite sfill_appl. exists. apply Step_save; eauto.
    + rewrite sfill_appl. destruct e1'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
  -  right. inverts Lc. 
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    inverts* Typ1;
    try solve [ inverts Val1 ].
    + forwards*: vval_dec Val1. destruct H3.
      * forwards*: vval_dec Val2. destruct H4.
        -- assert (Typing nil e1 Chk t_int); eauto.
           forwards*: TypedReduce_progress H5. destruct H6.
           lets H6': H6. 
           inverts H3; inverts H; inverts H0;
           inverts H6;
           try solve [exfalso; apply H10; eauto];
           try solve [simpl in H11; inverts* H11]. 
           ++ forwards*: TypedReduce_progress Typ2. destruct H.
              lets H': H. 
              inverts H4; inverts Typ2; inverts H0; inverts H4;
              inverts H;
              try solve [simpl in H14; inverts H14]. 
              ** exists. apply Step_addb; eauto.
              ** exists. apply Step_addb; eauto.
              ** exists. apply Step_addb; eauto.
              ** exists. apply Step_addb; eauto. 
              ** exists. apply Step_addr; eauto. unfold not; intros; inverts H. 
           ++ inverts H4. exists. apply Step_addb; eauto.
              exists. inverts H2. apply Step_addr; eauto. unfold not; intros nt; inverts nt.
           ++ exists. apply Step_addl; eauto. unfold not; intros; inverts H.
           ++ exists. apply Step_addl; eauto. unfold not; intros; inverts H.
        -- inverts* Val2;
           try solve [exfalso; apply H4; eauto].
           exists. rewrite sfill_addr.
           apply Step_save; eauto.
      * inverts* Val1;
           try solve [exfalso; apply H3; eauto].
           exists. rewrite sfill_addl.
           apply Step_save; eauto.  
    + forwards*: vval_dec Val1. destruct H.
      rewrite sfill_addr. destruct e2'.
      exists. apply do_step; eauto.
      exists. apply blame_step; eauto.
      inverts* Val1;
           try solve [exfalso; apply H; eauto].
           exists. rewrite sfill_addl.
           apply Step_save; eauto.
    + rewrite sfill_addl. destruct e1'. exists.
    apply do_step; eauto. exists. apply blame_step; eauto.
  -  Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      forwards*: TypedReduce_progress Val.
      inverts H.
      right. 
      exists. apply Step_annov; eauto. 
    + assert (lc_exp (e_anno e A)); eauto.
      forwards*: value_decidable H. inverts H1.
      left. auto.
      right. inductions t'. 
      exists. apply Step_anno; eauto. 
      exists. apply Step_annob; eauto. 
  - forwards*: IHTyp Typ.
Qed.
    
      