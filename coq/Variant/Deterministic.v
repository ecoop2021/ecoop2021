Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        rules_inf
        Typing
        Infrastructure.

Require Import Strings.String.

Lemma sim_refl: forall A,
  sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma TypedReduce_unique: forall v r1 r2 (A: typ),
    value v -> (exists B, Typing nil v Inf B) -> TypedReduce v A r1 -> TypedReduce v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2.
  lets R1': R1.
  induction R1; introv R2;
    try solve [inverts* R2].
Qed.


Lemma cTypedReduce_unique: forall v r1 r2 (A: typ),
    value v -> (exists B, Typing nil v Inf B) -> cTypedReduce v A r1 -> cTypedReduce v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2.
  lets R1': R1.
  induction R1; introv R2;
    try solve [inverts* R2].
Qed.

Lemma vval_val: forall v,
  vvalue v -> value v.
Proof.
  introv val.
  inductions val; eauto.
Qed.

Lemma sfill_eq: forall E0 e0 E e1 r1 r2,
  simpl_fill E0 e0 = simpl_fill E e1 ->
  step e0 r1 ->
  step e1 r2 ->
  simpl_wf E ->
  simpl_wf E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen E e0 e1 r1 r2.
  inductions E0; unfold simpl_fill in *;  intros.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: vval_val H0.
    forwards*: step_not_value red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: vval_val H0.
    forwards*: step_not_value red2.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: vval_val H0.
    forwards*: step_not_value red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: vval_val H0.
    forwards*: step_not_value red2.
Qed.


Lemma csfill_eq: forall E0 e0 E e1 r1 r2,
  simpl_fill E0 e0 = simpl_fill E e1 ->
  cstep e0 r1 ->
  cstep e1 r2 ->
  simpl_wf E ->
  simpl_wf E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen E e0 e1 r1 r2.
  inductions E0; unfold simpl_fill in *;  intros.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: vval_val H0.
    forwards*: cstep_not_value red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: vval_val H0.
    forwards*: cstep_not_value red2.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: vval_val H0.
    forwards*: cstep_not_value red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: vval_val H0.
    forwards*: cstep_not_value red2.
Qed.



Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - inverts* Red2. destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
  - inverts* Red2. destruct E; unfold simpl_fill in H; inverts* H.
    destruct E; unfold simpl_fill in H; inverts* H.
    destruct E; unfold simpl_fill in H; inverts* H.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    + forwards*: sfill_eq H0.
      destruct H3. subst. inverts Typ.
      destruct E0; unfold simpl_fill in H3. inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
    + forwards*: sfill_eq H0.
      destruct H3. subst. inverts Typ.
      destruct E0; unfold simpl_fill in H3. inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: vval_val H2. forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: vval_val H1.
      forwards*: step_not_value Red1.
      forwards*: vval_val H2. forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: vval_val H1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H1; inverts* H1.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      destruct E0; unfold simpl_fill in H4; inverts* H4.
      forwards*: step_not_value Red1.
      unfold simpl_fill in *. inverts H1.
      forwards*: vval_val H3. forwards*: step_not_value Red1.
      destruct E0; unfold simpl_fill in H4; inverts* H4. inverts H.
      inverts H3.  forwards*: step_not_value Red1.
      destruct E0; unfold simpl_fill in H4; inverts* H4.
      forwards*: step_not_value Red1.
      inverts H1. forwards*: vval_val H3. forwards*: step_not_value Red1.
      destruct E0; unfold simpl_fill in H4; inverts* H4. inverts H.
      inverts H3.  forwards*: step_not_value Red1.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    + forwards*: sfill_eq H0.
      destruct H3. subst. inverts Typ.
      destruct E0; unfold simpl_fill in H3. inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
     forwards*: step_not_value Red1.
     forwards*: vval_val H2. forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H1; inverts* H1.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence].
    forwards*: step_not_value H2 Red1.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence].
    forwards*: step_not_value H2 Red1.
  - inverts* Red2.
    destruct E; unfold simpl_fill in H1; inverts* H1; simpl in *.
    inverts* H3.
    destruct E; unfold simpl_fill in H1; inverts* H1.
    exfalso. apply H7. eauto.
    inverts H5.
    forwards*: vval_val H0.
    forwards*: step_not_value H3.
    destruct E; unfold simpl_fill in H1; inverts* H1.
    forwards*: step_not_value H3.
    forwards*: vval_val H0.
    forwards*: step_not_value H3.
    destruct E; unfold simpl_fill in H1; inverts* H1; inverts H0.
  - inverts Red2.
    destruct E; unfold simpl_fill in H2; inverts* H2;
    try solve [forwards*: vval_val H;
    forwards*: step_not_value H4];
    try solve [forwards*: vval_val H0;
    forwards*: step_not_value H4] .
    destruct E; unfold simpl_fill in H2; inverts* H2;
    try solve [forwards*: vval_val H;
    forwards*: step_not_value H5];
    try solve [forwards*: vval_val H0;
    forwards*: step_not_value H5]. inverts Typ. inverts H2. inverts H10. forwards*: vval_val H.
    reflexivity.
    exfalso. apply H1. eauto.
    exfalso. apply H1. eauto.
    destruct E; unfold simpl_fill in H2; inverts* H2. inverts H. inverts H0.
  - inverts Red2.
    destruct E; unfold simpl_fill in H1; inverts* H1;
    try solve [forwards*: vval_val H;
    forwards*: step_not_value H3];
    try solve [forwards*: vval_val H0;
    forwards*: step_not_value H3] .
    destruct E; unfold simpl_fill in H1; inverts* H1;
    try solve [forwards*: vval_val H;
    forwards*: step_not_value H4];
    try solve [forwards*: vval_val H0;
    forwards*: step_not_value H4].  exfalso. apply H6. eauto. 
    reflexivity.
    exfalso. apply H0. eauto.
    reflexivity. 
  - inverts* Red2.
    destruct E; unfold simpl_fill in H; inverts* H; simpl in *.
    forwards*: step_not_value H1.
    forwards*: step_not_value H1.
    destruct E; unfold simpl_fill in H; inverts* H; simpl in *.
    forwards*: step_not_value H1.
    forwards*: step_not_value H1.
    exfalso. apply H4. eauto.
    exfalso. apply H4. eauto.
    destruct E; unfold simpl_fill in H; inverts* H. 
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    forwards*: step_not_value H3. forwards*: step_not_value H3.
    inverts Typ. inverts H1. inverts H7.
    forwards*: TypedReduce_unique H0 H5. 
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2].
     destruct E; unfold simpl_fill in H1; inverts* H1.
      destruct E0; unfold simpl_fill in H5; inverts* H5.
      forwards*: step_not_value H3. inverts H2. inverts H4.
      destruct E0; unfold simpl_fill in H5; inverts* H5. inverts H.
      forwards*: vval_val H4. forwards*: step_not_value H3.
      forwards*: step_not_value H3.
      destruct E0; unfold simpl_fill in H5; inverts* H5.
      forwards*: step_not_value H3.
      inverts H2. inverts H4. 
      destruct E0; unfold simpl_fill in H5; inverts* H5. inverts H.
      forwards*: vval_val H4. forwards*: step_not_value H3.
      forwards*: step_not_value H3.
    destruct E; unfold simpl_fill in H1; inverts* H1. inverts H3.
    destruct E; unfold simpl_fill in H2; inverts* H2. 
Qed.


Theorem cstep_unique: forall A e r1 r2,
    Typing nil e Chk A -> cstep e r1 -> cstep e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - inverts* Red2. destruct E; unfold simpl_fill in H0; inverts* H0.
  - inverts* Red2. destruct E; unfold simpl_fill in H; inverts* H.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    + forwards*: csfill_eq H0.
      destruct H3. subst. inverts Typ.
      destruct E0; unfold simpl_fill in H3. inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: cstep_not_value Red1.
      forwards*: vval_val H2. forwards*: cstep_not_value Red1.
    + destruct E; unfold simpl_fill in H1; inverts* H1.
      forwards*: cstep_not_value Red1.
      forwards*: cstep_not_value Red1.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence].
    forwards*: cstep_not_value H2 Red1.
  - inverts* Red2.
    destruct E; unfold simpl_fill in H1; inverts* H1; simpl in *.
    inverts* H3.
    destruct E; unfold simpl_fill in H1; inverts* H1.
    exfalso. apply H7. eauto.
    inverts H5.
    forwards*: vval_val H0.
    forwards*: cstep_not_value H3.
  - inverts Red2.
    destruct E; unfold simpl_fill in H; inverts* H;
    try solve [
    forwards*: cstep_not_value H1];
    try solve [
    forwards*: cstep_not_value H1] .
    reflexivity.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    forwards*: cstep_not_value H3. 
    inverts Typ. inverts H1. inverts H7.
    forwards*: cTypedReduce_unique H0 H5. 
Qed.
