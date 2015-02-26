Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.ListType.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

Ltac lf_fold_type :=
  match goal with
    | _ : listS ?e = Some (pFold ?t ?u), _ : ExprDsimul.ExprDenote.exprD' _ _
       (typ2 (typ2 ?u (typ2 ?t ?t)) (typ2 ?t (typ2 (tyList ?u) ?t))) ?e =
     Some _ |- _ => fail 1
	| H1 : listS ?e = Some (pFold _ _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _ |- _ =>
	  let H := fresh "H" in
	     pose proof (lf_fold_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
  end.
  
Ltac lf_fold_expr :=
  match goal with
    | _ : listS ?e = Some (pFold ?t ?u),
      _ : ExprDsimul.ExprDenote.exprD' ?tus ?tvs
       (typ2 (typ2 ?u (typ2 ?t ?t)) (typ2 ?t (typ2 (tyList ?u) ?t))) ?e =
     Some (fun _ _ => foldD ?t ?u) |- _ => fail 1
	| H1 : listS ?e = Some (pFold _ _),
	  H2 : ExprDsimul.ExprDenote.exprD' _ _  (typ2 (typ2 ?u (typ2 ?t ?t)) (typ2 ?t (typ2 (tyList ?u) ?t))) ?e = Some _ |- _ =>
	  let H := fresh "H" in pose proof(lf_fold_eq _ H1 H2); subst
  end.

Ltac lf_map_type :=
  match goal with
    | _ : listS ?e = Some (pMap ?t ?u), _ : ExprDsimul.ExprDenote.exprD' _ _ 
       (typ2 (typ2 ?t ?u) (typ2 (tyList ?t) (tyList ?u))) ?e =
     Some _ |- _ => fail 1
	| H1 : listS ?e = Some (pMap _ _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _ |- _ =>
	  let H := fresh "H" in
	     pose proof (lf_map_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
  end.
  
Ltac lf_map_expr :=
  match goal with
    | _ : listS ?e = Some (pMap ?t ?u),
      _ : ExprDsimul.ExprDenote.exprD' ?tus ?tvs
       (typ2 (typ2 ?t ?u) (typ2 (tyList ?t) (tyList ?u))) ?e =
     Some (fun _ _ => mapD ?t ?u) |- _ => fail 1
	| H1 : listS ?e = Some (pMap _ _),
	  H2 : ExprDsimul.ExprDenote.exprD' _ _  (typ2 (typ2 ?t ?u) (typ2 (tyList ?t) (tyList ?u))) ?e = Some _ |- _ =>
	  let H := fresh "H" in pose proof(lf_map_eq _ H1 H2); subst
  end.

Ltac lf_nil_type :=
  match goal with
    | _ : listS ?e = Some (pNil ?t), _ : ExprDsimul.ExprDenote.exprD' ?tus ?tvs (tyList ?t) ?e = Some _ |- _ => fail 1
	| H1 : listS ?e = Some (pNil _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _ |- _ =>
	  let H := fresh "H" in
	     pose proof (lf_nil_type_eq _ _ H1 H2) as H; try list_inj H; repeat clear_eq; subst
  end.

Ltac lf_nil_expr :=
  match goal with
    | _ : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) ?e = Some (fun _ _ => nilD ?t) |- _ => fail 1
	| H1 : listS ?e = Some (pNil _), H2 : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) ?e = Some _ |- _ =>
	  pose proof(lf_nil_eq _ H1 H2); subst
  end.

Ltac lf_cons_expr :=
  match goal with
    | _ : listS ?e = Some (pCons ?t),
      _ : ExprDsimul.ExprDenote.exprD' ?tus ?tvs  ?e =
     Some (fun _ _ => consD ?t) |- _ => fail 1
	| H1 : listS ?e = Some (pCons ?t),
	  H2 : ExprDsimul.ExprDenote.exprD' ?tus ?tvs (typ2 ?t (typ2 (tyList ?t) (tyList ?t))) ?e = Some _|- _ =>
	  let H := fresh "H" in pose proof(lf_cons_eq _ H1 H2); subst
	| H : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) (mkCons ?t _ _) = Some _ |- _ =>
	  pose proof (mkConsD _ _ _ H); clear H; (repeat destruct_match_oneres)
  end.

Ltac lf_forward_step :=
  match goal with 
    | H : Some _ = listS _ |- _ =>  symmetry in H
    | _ => 
       first [
        lf_nil_type |
        lf_fold_type |
        lf_map_type |
        lf_nil_expr |
        lf_cons_expr |
        lf_fold_expr |
        lf_map_expr
      ]
  end.
 