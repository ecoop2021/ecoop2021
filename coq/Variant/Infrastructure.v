Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf.

Require Import List. Import ListNotations.
Require Import Strings.String.


Definition irred e : Prop := forall b, ~(step e b).
Definition cirred e : Prop := forall b, ~(cstep e b).



Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).


Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "v ~-> A v'" := (TypedReduce v A v') (at level 68).

Notation "t ->* r" := (steps t r) (at level 68). 


Lemma star_one:
forall a b, cstep a (Expr b) -> steps a (Expr b).
Proof.
eauto using steps.
Qed.

Lemma star_trans:
forall a b, steps a (Expr b) -> forall c, steps b (Expr c) -> steps a (Expr c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Hint Resolve star_one star_trans : core.




(** [x # E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` F).




Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H.
  eapply lc_e_save.
  inverts* H. 
Qed.



Lemma step_not_value: forall (v:exp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros.
  - inverts* H.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
  - inverts* H.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
  - inverts* H.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
Qed.

Lemma cstep_not_value: forall (v:exp),
    value v -> cirred v.
Proof.
  introv.
  unfold cirred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros.
  - inverts* H.
    destruct E; unfold simpl_fill in H0; inverts* H0.
  - inverts* H.
    destruct E; unfold simpl_fill in H0; inverts* H0.
  - inverts* H.
    destruct E; unfold simpl_fill in H0; inverts* H0.
Qed.


Lemma multi_red_app : forall v t t',
    vvalue v -> t ->* (Expr t') -> (e_app v t) ->* (Expr (e_app v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(simpl_wf (sappCtxR v)). eauto.
  forwards*: cdo_step H1 H.
Qed.

Lemma multi_red_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_app t1 t2) ->* (Expr (e_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(simpl_wf (sappCtxL t2)). eauto.
  forwards*: cdo_step H0 H.
Qed.

Lemma multi_red_add : forall v t t',
    vvalue v -> t ->* (Expr t') -> (e_add v t) ->* (Expr (e_add v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(simpl_wf (saddCtxR v)). eauto.
  forwards*: cdo_step H1 H.
Qed.

Lemma multi_red_add2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_app t1 t2) ->* (Expr (e_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(simpl_wf (sappCtxL t2)). eauto.
  forwards*: cdo_step H0 H.
Qed.



