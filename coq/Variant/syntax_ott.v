
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.

(** syntax *)
Definition i : Set := nat.
Definition b : Set := bool.

Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_arrow (A:typ) (B:typ) (*r function types *)
 | t_dyn : typ (*r dynamic type *).

Inductive st : Set :=  (*r input type or projection label *)
 | st_ty (A:typ).

 Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (A:typ) (e:exp) (B:typ) (*r abstractions *)
 | e_app (e1:exp) (e2:exp) (*r applications *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_add (e1:exp) (e2:exp) (*r addistion *)
 | e_save (e:exp) (A:typ) (*r save *).

 Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

 Definition ctx : Set := list ( atom * typ ).

 Definition ls : Set := list st.
 

 (** opening up abstractions *)
 Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
    match e__6 with
    | (e_var_b nat) => 
        match lt_eq_lt_dec nat k with
          | inleft (left _) => e_var_b nat
          | inleft (right _) => e_5
          | inright _ => e_var_b (nat - 1)
        end
    | (e_var_f x) => e_var_f x
    | (e_lit i5) => e_lit i5
    | (e_abs A e B) => e_abs A (open_exp_wrt_exp_rec (S k) e_5 e) B
    | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
    | (e_add e1 e2) => e_add (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (e_save e A) => e_save (open_exp_wrt_exp_rec k e_5 e) A
  end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (A:typ) (e:exp) (B:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A e B))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 | lc_e_add : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_add e1 e2))
 | lc_e_save : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_save e A)).


(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_abs A e B) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  | (e_add e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_save e A) => (fv_exp e)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs A e B) => e_abs A (subst_exp e_5 x5 e) B
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | (e_add e1 e2) => e_add (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_save e A) => e_save (subst_exp e_5 x5 e) A
end.


(* principal types for values*)
Fixpoint principal_type (v:exp) : typ :=
  match v with
  | (e_lit i5) => t_int
  | (e_abs A e B) => (t_arrow A B)
  | (e_anno e A) => A
  | (e_save e A) => A
  | _ => t_dyn
  end.


Inductive sval : exp -> Prop :=    (* defn fval *)
 | sval_abs : forall (A:typ) (e:exp) (B:typ),
     lc_exp (e_abs A e B) ->
     sval  ( (e_abs A e B) )
 | sval_i : forall i5,
     sval  ( (e_lit i5) ).

(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_lit : forall (i5:i) (A: typ),
     value (e_anno (e_lit i5) A)
 | value_abs : forall (A:typ) (e:exp) (B C:typ),
     lc_exp (e_abs A e B) ->
     value  ( (e_anno  ( (e_abs A e B) )  C) ) 
 | value_save : forall (e:exp) (A:typ),
     sval e ->
     value  ( (e_save e A) ) .

(* defns vValues *)
Inductive vvalue : exp -> Prop :=    (* defn value *)
 | vvalue_lit : forall (i5:i) (A: typ),
     vvalue (e_anno (e_lit i5) A)
 | vvalue_abs : forall (A:typ) (e:exp) (B C:typ),
     lc_exp (e_abs A e B) ->
     vvalue  ( (e_anno  ( (e_abs A e B) )  C) ).

Inductive ival : exp -> Prop :=    (* defn value *)
 | ival_lit : forall (i5:i) (A: typ),
     ival (e_anno (e_lit i5) A).

(* defns Consistency *)
Inductive sim : typ -> typ -> Prop :=    (* defn sim *)
 | S_i : 
     sim t_int t_int
 | S_arr : forall (A B C D:typ),
     sim A C ->
     sim B D ->
     sim (t_arrow A B) (t_arrow C D)
 | S_dynl : forall (A:typ),
     sim t_dyn A
 | S_dynr : forall (A:typ),
     sim A t_dyn.


(* defns Typing *)
Inductive Typing : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Typing G (e_lit i5) Inf t_int
 | Typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Typing G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     Typing G (e_abs A e B) Inf (t_arrow A B)
 | Typ_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     Typing G e1 Inf (t_arrow A B) ->
     Typing G e2 Chk A ->
     Typing G (e_app e1 e2) Inf B
 | Typ_add : forall (G:ctx) (e1 e2:exp),
     Typing G e1 Chk t_int ->
     Typing G e2 Chk t_int ->
     Typing G (e_add e1 e2) Inf t_int
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ),
     Typing G e Chk A ->
     Typing G  ( (e_anno e A) )  Inf A
 | Typ_save : forall (G:ctx) (e:exp) (A B:typ),
      uniq  G  ->
     sval e ->
     Typing  nil  e Inf B ->
      not (  sim B A  )  ->
     Typing G  ( (e_save e A) )  Inf A
 | Typ_sim : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     sim A B ->
     Typing G e Chk B.



Inductive simpl_item : Type :=
     | sappCtxL : exp -> simpl_item
     | sappCtxR : exp -> simpl_item
     | saddCtxL : exp -> simpl_item
     | saddCtxR : exp -> simpl_item.
   


Inductive simpl_wf : simpl_item -> Prop :=
     | swf_appl : forall (e : exp),
                    simpl_wf (sappCtxL e)
     | swf_appr : forall (v : exp),
                    vvalue v ->
                    simpl_wf (sappCtxR v)
     | swf_addl : forall (e : exp),
                    simpl_wf (saddCtxL e)
     | swf_addr : forall (v : exp),
                    vvalue v ->
                    simpl_wf (saddCtxR v).


Definition simpl_fill (EE : simpl_item) (e : exp) : exp :=
     match EE with
     | sappCtxL e2 => e_app e e2
     | sappCtxR v1 => e_app v1 e
     | saddCtxL e2 => e_add e e2
     | saddCtxR v1 => e_add v1 e
     end.
   
   
Inductive res : Type :=
     | Expr  : exp -> res
     | Blame :  res.

(* defns Semantics *)
Inductive TypedReduce : exp -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | TReduce_sim : forall (e:exp) (A:typ) (B:typ),
     lc_exp e ->
     sim (principal_type e) B ->
     TypedReduce  ( (e_anno e A) ) B  (Expr ( (e_anno e B) ))
 | TReduce_simp : forall (A:typ) (e:exp) (B:typ),
     lc_exp e ->
      not (  sim (principal_type e) B  )  ->
     TypedReduce  ( (e_anno e A) ) B  (Expr (e_save e B) ) 
 | TReduce_savep : forall (e:exp) (A B:typ),
     sim   (principal_type  e )   B ->
     TypedReduce  ( (e_save e A) )  B  (Expr (e_anno e B) ) 
 | TReduce_save : forall (e:exp) (A B:typ),
      not (  sim   (principal_type  e )   B  )  ->
     TypedReduce  ( (e_save e A) )  B  (Expr (e_save e B) ).


Inductive cTypedReduce : exp -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | cTReduce_sim : forall (e:exp) (A:typ) (B:typ),
     lc_exp e ->
     sim (principal_type e) B ->
     cTypedReduce  ( (e_anno e A) ) B  (Expr ( (e_anno e B) ))
 | cTReduce_savep : forall (e:exp) (A B:typ),
     sim   (principal_type  e )   B ->
     cTypedReduce  ( (e_save e A) )  B  (Expr (e_anno e B) ).

Inductive step : exp -> res -> Prop :=
   | Step_abs : forall (A:typ) (e:exp) (B:typ),
      lc_exp (e_abs A e B) ->
      step (e_abs A e B) (Expr (e_anno (e_abs A e B) (t_arrow A B)))
   | Step_i : forall (i5:i),
     step (e_lit i5) (Expr (e_anno (e_lit i5) t_int))
   | do_step E e1 e2 :
    simpl_wf E ->
    step e1 ( Expr e2 ) ->
    step (simpl_fill E e1) (Expr (simpl_fill E e2))
  | blame_step E e1 :
    simpl_wf E ->
    step e1 Blame ->
    step (simpl_fill E e1) Blame
   | Step_anno : forall (e e':exp ) (A: typ),
     step e (Expr e') ->
     not (value (e_anno e A)) -> 
     step (e_anno e A) (Expr (e_anno e' A))
   | Step_annob : forall (e:exp ) (A: typ),
     step e Blame ->
     not (value (e_anno e A)) -> 
     step (e_anno e A) Blame
   | Step_beta : forall (A1 A2:typ) (e:exp) (B1 B2:typ) (v : exp),
     lc_exp (e_abs A1 e B1) ->
     vvalue v ->
     step (e_app  (e_anno (e_abs A1 e B1) (t_arrow A2 B2))  v)  (Expr (e_anno (e_anno (open_exp_wrt_exp  e (e_anno (e_anno v A2) A1) ) B1) B2) ) 
   | Step_addl : forall v1 v2,
     vvalue v1 ->
     vvalue v2 ->
     not (ival v1) ->
     step (e_add v1 v2) Blame
   | Step_addr : forall i5 v2 A,
     vvalue v2 ->
     not ((ival v2)) ->
     step (e_add (e_anno (e_lit i5) A) v2) Blame
  | Step_addb : forall i1 i2 A B,
     step (e_add (e_anno (e_lit i1) A) (e_anno (e_lit i2) B)) (Expr (e_anno (e_lit (i1 + i2)) t_int))
  | Step_annov : forall (v:exp) (A:typ) (v':res),
     value v ->
     TypedReduce v A v' ->
     step (e_anno v A) v'
 | Step_save : forall (E : simpl_item) (e:exp) (A:typ),
     simpl_wf E ->
     sval e ->
     step (simpl_fill E (e_save e A)) Blame.

Inductive cstep : exp -> res -> Prop :=
   | cStep_abs : forall (A:typ) (e:exp) (B:typ),
      lc_exp (e_abs A e B) ->
      cstep (e_abs A e B) (Expr (e_anno (e_abs A e B) (t_arrow A B)))
   | cStep_i : forall (i5:i),
     cstep (e_lit i5) (Expr (e_anno (e_lit i5) t_int))
   | cdo_step E e1 e2 :
    simpl_wf E ->
    cstep e1 ( Expr e2 ) ->
    cstep (simpl_fill E e1) (Expr (simpl_fill E e2))
   | cStep_anno : forall (e e':exp ) (A: typ),
     cstep e (Expr e') ->
     not (value (e_anno e A)) -> 
     cstep (e_anno e A) (Expr (e_anno e' A))
   | cStep_beta : forall (A1 A2:typ) (e:exp) (B1 B2:typ) (v : exp),
     lc_exp (e_abs A1 e B1) ->
     vvalue v ->
     cstep (e_app  (e_anno (e_abs A1 e B1) (t_arrow A2 B2))  v)  (Expr (e_anno (e_anno (open_exp_wrt_exp  e (e_anno (e_anno v A2) A1) ) B1) B2) ) 
  | cStep_addb : forall i1 i2 A B,
     cstep (e_add (e_anno (e_lit i1) A) (e_anno (e_lit i2) B)) (Expr (e_anno (e_lit (i1 + i2)) t_int))
  | cStep_annov : forall (v:exp) (A:typ) (v':res),
     value v ->
     cTypedReduce v A v' ->
     cstep (e_anno v A) v'.

(* defns type precision *)
Inductive tpre : typ -> typ -> Prop :=    (* defn sim *)
 | tp_i : 
     tpre t_int t_int
 | tp_dyn : forall (A:typ),
     tpre A t_dyn
 | tp_abs : forall (A B C D:typ),
     tpre A C ->
     tpre B D ->
     tpre (t_arrow A B) (t_arrow C D).

(* defns expression precision *)
Inductive epre : exp -> exp -> Prop :=    (* defn sim *)
 | ep_refl e:
    lc_exp e ->
    epre e e 
 | ep_abs : forall (A1 A2:typ) (e1 e2:exp) (B1 B2:typ) (L:vars),
     ( forall x , x \notin  L  -> 
      epre  ( open_exp_wrt_exp e1 (e_var_f x) )   ( open_exp_wrt_exp e2 (e_var_f x) )  )  ->
     tpre A1 A2 ->
     tpre B1 B2 ->
     epre (e_abs A1 e1 B1) (e_abs A2 e2 B2)
 | ep_app : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_app e1' e2')
 | ep_add : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_add e1 e2) (e_add e1' e2')
 | ep_anno : forall (A B:typ) (e1 e2:exp),
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 A) (e_anno e2 B)
 | ep_save : forall (A B:typ) (e1 e2:exp),
     tpre A B ->
     epre e1 e2 ->
     epre (e_save e1 A) (e_save e2 B).

Inductive steps : exp -> res -> Prop :=
  | step_refl e:
    steps e (Expr e)

  | step_n e t' e':   
    cstep e (Expr e') ->
    steps e' (Expr t') ->
    steps e  (Expr t').


(** infrastructure *)
Hint Constructors value sval vvalue ival sim cTypedReduce TypedReduce simpl_wf cstep step steps tpre epre Typing lc_exp : core.


