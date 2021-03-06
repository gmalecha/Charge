(*---------------------------------------------------------------------------
    This file axiomatises the inference rules of an intuitionistic logic and
    offers some parametric instances to make it straightforward to create a new
    logic that satisfies those axioms. The purpose is to factor out what the
    assertion logic and specification logic of a separation logic framework
    have in common.
  ---------------------------------------------------------------------------*)
Require Import Setoid.
Require Import Morphisms.
Require Import RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

Set Maximal Implicit Insertion.

Existing Class inhabited.

Generalizable Variables Frm.

(* Logical connectives *)
Class ILogicOps Frm := {
  lentails: relation Frm;
  ltrue: Frm;
  lfalse: Frm;
  limpl: Frm -> Frm -> Frm;
  land: Frm -> Frm -> Frm;
  lor: Frm -> Frm -> Frm;
  lforall: forall {T}, (T -> Frm) -> Frm;
  lexists: forall {T}, (T -> Frm) -> Frm
}.

(* These notations have to sit strictly between level 80 (precendence of /\)
   and level 70 (precedence of =). *)
Infix "|--"  := lentails (at level 79, no associativity).
Infix "//\\"   := land (at level 75, right associativity).
Infix "\\//"   := lor (at level 76, right associativity).
Infix "-->>"   := limpl (at level 77, right associativity).
Notation "'Forall' x : T , p" :=
  (lforall (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Forall' x , p" :=
  (lforall (fun x => p)) (at level 78, x ident, right associativity, only parsing).
Notation "'Exists' x : T , p" :=
  (lexists (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Exists' x , p" :=
  (lexists (fun x => p)) (at level 78, x ident, right associativity, only parsing).

Section ILogicEquiv.
  Context `{IL: ILogicOps Frm}.

  Definition lequiv P Q := P |-- Q /\ Q |-- P.
End ILogicEquiv.

Infix "-|-"  := lequiv (at level 85, no associativity).

(* Axioms of an intuitionistic logic, presented in a sequent calculus style
   with singleton contexts on the left of the turnstile. This form is
   particularly suited for the undisciplined context manipulation that tends to
   happen in separation logic.

   Every connective has a number of L-rules and a number of R-rules describing
   what can be done to prove a goal that has the connective as the head symbol
   of the left, respectively right, side of a turnstile. The notable exception
   to this pattern is implication, which is required to be the right adjoint of
   conjunction. This makes singleton contexts work. *)
Class ILogic Frm {ILOps: ILogicOps Frm} := {
  lentailsPre:> PreOrder lentails;
  ltrueR: forall C, C |-- ltrue;
  lfalseL: forall C, lfalse |-- C;
  lforallL: forall T x (P: T -> Frm) C, P x |-- C -> lforall P |-- C;
  lforallR: forall T (P: T -> Frm) C, (forall x, C |-- P x) -> C |-- lforall P;
  lexistsL: forall T (P: T -> Frm) C, (forall x, P x |-- C) -> lexists P |-- C;
  lexistsR: forall T x (P: T -> Frm) C, C |-- P x -> C |-- lexists P;
  landL1: forall P Q C, P |-- C  ->  P //\\ Q |-- C;
  landL2: forall P Q C, Q |-- C  ->  P //\\ Q |-- C;
  lorR1:  forall P Q C, C |-- P  ->  C |-- P \\// Q;
  lorR2:  forall P Q C, C |-- Q  ->  C |-- P \\// Q;
  landR:  forall P Q C, C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q;
  lorL:   forall P Q C, P |-- C  ->  Q |-- C  ->  P \\// Q |-- C;
  landAdj: forall P Q C, C |-- (P -->> Q) -> C //\\ P |-- Q;
  limplAdj: forall P Q C, C //\\ P |-- Q -> C |-- (P -->> Q)
}.
Implicit Arguments ILogic [[ILOps]].
Implicit Arguments lforallL [[ILOps] [Frm] [ILogic] [T] [P] [C]].
Implicit Arguments lexistsR [[ILOps] [Frm] [ILogic] [T] [P] [C]].

Notation "|--  P" := (ltrue |-- P) (at level 85, no associativity).
Hint Extern 0 (?x |-- ?x) => reflexivity.
Hint Extern 0 (_ |-- ltrue) => apply ltrueR.
Hint Extern 0 (lfalse |-- _) => apply lfalseL.
Hint Extern 0 (?P |-- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).

Section ILogicEquiv2.
  Context `{IL: ILogic Frm}.

  Global Instance lequivEquivalence : Equivalence lequiv.
  Proof.
    unfold lequiv. constructor; red.
    + split; reflexivity.
    + intuition.
    + intros P Q R [HPQ HQP] [HQR HRQ];
      split; etransitivity; eassumption.
  Qed.

End ILogicEquiv2.


(* Most of the connectives in ILogicOps are redundant. They can be derived from
   lexists, lforall and limpl, and the choice of limpl is unique up to lequiv
   since it is an adjoint. *)

Section ILogicEquivOps.
  Context `{IL: ILogic Frm}.

  Lemma land_is_forall P Q :
    P //\\ Q -|- Forall b : bool, if b then P else Q.
  Proof.
    split.
    - apply lforallR; intro x; destruct x.
      + apply landL1; reflexivity.
      + apply landL2; reflexivity.
    - apply landR.
      + apply lforallL with true; reflexivity.
      + apply lforallL with false; reflexivity.
  Qed.

  Lemma lor_is_exists P Q:
    P \\// Q -|- Exists b : bool, if b then P else Q.
  Proof.
    split.
    - apply lorL.
      + apply lexistsR with true; reflexivity.
      + apply lexistsR with false; reflexivity.
    - apply lexistsL; intro x; destruct x.
      + apply lorR1; reflexivity.
      + apply lorR2; reflexivity.
  Qed.

  Lemma ltrue_is_forall:
    ltrue -|- Forall x: Empty_set, Empty_set_rect _ x.
  Proof.
    split; [apply lforallR|]; intuition.
  Qed.

  Lemma lfalse_is_exists:
    lfalse -|- Exists x: Empty_set, Empty_set_rect _ x.
  Proof. split; [|apply lexistsL]; intuition. Qed.

End ILogicEquivOps.

Section ILogicMorphisms.
  Context `{IL: ILogic Frm}.

  Global Instance lequiv_lentails : subrelation lequiv lentails.
  Proof. firstorder. Qed.
  Global Instance lequiv_inverse_lentails: subrelation lequiv (inverse lentails).
  Proof. firstorder. Qed.

  Global Instance lforall_lentails_m T:
    Proper (pointwise_relation T lentails ++> lentails) lforall.
  Proof.
    intros P P' HP. apply lforallR; intro x;  apply lforallL with x.
    rewrite HP; reflexivity.
  Qed.

  Global Instance lforall_lequiv_m T:
    Proper (pointwise_relation T lequiv ++> lequiv) lforall.
  Proof.
    intros P P' HP; split; apply lforall_lentails_m; intro x; apply HP.
  Qed.

  Global Instance lexists_lentails_m T:
    Proper (pointwise_relation T lentails ++> lentails) lexists.
  Proof.
    intros P P' HP. apply lexistsL; intro x; apply lexistsR with x.
    rewrite HP; reflexivity.
  Qed.

  Global Instance lexists_lequiv_m T:
    Proper (pointwise_relation T lequiv ++> lequiv) lexists.
  Proof.
    intros P P' HP; split; apply lexists_lentails_m; intro x; apply HP.
  Qed.

  Global Instance : Proper (lequiv ==> lequiv ==> iff) lequiv.
  Proof.
    intros P P' HP Q Q' HQ; split; intros H.
    + rewrite <- HP; rewrite <- HQ; assumption.
    + rewrite HP; rewrite HQ; assumption.
  Qed.

  Global Instance lequiv_lentails_m : Proper (lequiv ==> lequiv ==> iff) lentails.
  Proof.
    cbv; intuition; (etransitivity; [etransitivity|]); eassumption.
  Qed.

  Global Instance lentails_lentails_m: Proper (lentails --> lentails ++> Basics.impl) lentails.
  Proof.
    intuition.
  Qed.

  Global Instance land_lentails_m:
    Proper (lentails ++> lentails ++> lentails) land.
  Proof.
    intros P P' HP Q Q' HQ.
    apply landR; [apply landL1 | apply landL2]; assumption.
  Qed.

  Global Instance land_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) land.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply land_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lor_lentails_m:
    Proper (lentails ++> lentails ++> lentails) lor.
  Proof.
    intros P P' HP Q Q' HQ.
    apply lorL; [apply lorR1 | apply lorR2]; assumption.
  Qed.

  Global Instance lor_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lor.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lor_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance limpl_lentails_m:
    Proper (lentails --> lentails ++> lentails) limpl.
  Proof.
    intros P P' HP Q Q' HQ; red in HP.
    apply limplAdj; rewrite <- HQ, HP; apply landAdj; reflexivity.
  Qed.

  Global Instance limpl_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) limpl.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply limpl_lentails_m; (apply HP || apply HQ).
  Qed.

End ILogicMorphisms.

Hint Extern 0 (?x -|- ?x) => reflexivity.
Hint Extern 0 (?P -|- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).

(* TODO: also add lforwardR. *)
Lemma lforwardL {Frm} `{IL: ILogic Frm} {Q R}:
    Q |-- R -> forall P G,
    P |-- Q ->
    (P |-- R -> G) ->
    G.
Proof. intros HQR ** HPQ HG. apply HG. etransitivity; eassumption. Qed.

Tactic Notation "lforwardL" hyp(H) :=
  eapply (lforwardL H); clear H; [|intros H].

Section ILogicFacts.
  Context `{IL: ILogic Frm}.

  (* Experiments with proof search. *)
  Ltac landR :=
    repeat match goal with
    | |- _ |-- _ //\\ _ => apply landR
    end.

  Ltac landL :=
    repeat match goal with
    | |- ?L1 //\\ ?L2 |-- ?R =>
        match L1 with
        | context [R] => apply landL1
        | _ =>
          match L2 with
          | context [R] => apply landL2
          end
        end
    end.

  Lemma landC P Q: P //\\ Q -|- Q //\\ P.
  Proof. split; landR; landL; reflexivity. Qed.

  Lemma landA P Q R: (P //\\ Q) //\\ R -|- P //\\ (Q //\\ R).
  Proof. split; landR; landL; reflexivity. Qed.

  Lemma lorC P Q : P \\// Q -|- Q \\// P.
  Proof.
    split; apply lorL; [apply lorR2 | apply lorR1 | apply lorR2 | apply lorR1]; reflexivity.
  Qed.

  Lemma lorA P Q R : (P \\// Q) \\// R -|- P \\// (Q \\// R).
  Proof.
  	split; apply lorL; try apply lorL; [
  	   apply lorR1 |
       apply lorR2; apply lorR1 |
       apply lorR2; apply lorR2 |
       apply lorR1; apply lorR1 |
       apply lorR1; apply lorR2 |
       apply lorR2
     ]; reflexivity.
   Qed.

  (* Special case of limplAdj/landAdj when there is just ltrue on the lhs *)
  Lemma limplValid P Q:
    |-- P -->> Q <->
    P |-- Q.
  Proof.
    split; intro H.
    - etransitivity; [eapply landR; [apply ltrueR|reflexivity]|].
      apply landAdj; assumption.
    - apply limplAdj. apply landL2; assumption.
  Qed.

  (* Left-rule for limpl. This breaks the discipline of the ILogic presentation
     since the implication is not strictly the top symbol of the left-hand side,
     but it remains a convenient rule. *)
  Lemma limplL P Q CL CR (HP: CL |-- P) (HR: Q //\\ CL |-- CR) :
    (P -->> Q) //\\ CL |-- CR.
  Proof.
    rewrite <-HR, <-HP. apply landR; [apply landAdj |apply landL2]; reflexivity.
  Qed.

  Lemma limplAdj2 P Q R : P -->> Q -->> R -|- P //\\ Q -->> R.
  Proof.
  	split.
  	+ apply limplAdj. do 2 (apply limplL; [landL; reflexivity|]).
  	  landL. reflexivity.
    + do 2 apply limplAdj; rewrite landA.
      apply limplL; [reflexivity | landL; reflexivity].
  Qed.

  Lemma landexistsDL {A} (f : A -> Frm) (P : Frm) :
    (Exists a, f a) //\\ P |-- Exists a, (f a //\\ P).
  Proof.
    apply landAdj; apply lexistsL; intro a;
    apply limplAdj; apply lexistsR with a; reflexivity.
  Qed.


  Lemma landexistsDR {A} (f : A -> Frm) (P : Frm) :
     Exists a, (f a //\\ P) |-- (Exists a, f a) //\\ P.
  Proof.
    apply lexistsL; intro a; apply landR.
    - apply landL1; apply lexistsR with a; reflexivity.
    - apply landL2; reflexivity.
  Qed.

  Lemma landexistsD {A} (f : A -> Frm) (P : Frm) :
    (Exists a, f a) //\\ P -|- Exists a, (f a //\\ P).
  Proof.
    split; [apply landexistsDL | apply landexistsDR].
  Qed.

  Lemma lorexistsDL {A} (f : A -> Frm) (P : Frm) {H : inhabited A} :
    (Exists a, f a) \\// P |-- Exists a, (f a \\// P).
  Proof.
    apply lorL.
    + apply lexistsL; intro x; apply lexistsR with x; apply lorR1; reflexivity.
    + destruct H. eapply lexistsR with X. apply lorR2; reflexivity.
  Qed.


  Lemma lorexistsDR {A} (f : A -> Frm) (P : Frm) :
     Exists a, (f a \\// P) |-- (Exists a, f a) \\// P.
  Proof.
  	apply lexistsL; intro x; apply lorL.
  	+ apply lorR1; apply lexistsR with x; reflexivity.
  	+ apply lorR2; reflexivity.
  Qed.

  Lemma lorexistsD {A} (f : A -> Frm) (P : Frm) {H : inhabited A} :
    (Exists a, f a) \\// P -|- Exists a, (f a \\// P).
  Proof.
    split; [apply lorexistsDL; apply H| apply lorexistsDR].
  Qed.

  Lemma landforallDL {A} (f : A -> Frm) (P : Frm) :
    (Forall a, f a) //\\ P |-- Forall a, (f a //\\ P).
  Proof.
    apply lforallR; intro a; apply landR.
    + apply landL1; apply lforallL with a; reflexivity.
    + apply landL2; reflexivity.
  Qed.

  Lemma landforallDR {A} {H: inhabited A} (f : A -> Frm) (P : Frm) :
    Forall a, (f a //\\ P) |-- (Forall a, f a) //\\ P.
  Proof.
    apply landR.
    + apply lforallR; intro a; apply lforallL with a; apply landL1; reflexivity.
    + destruct H. apply lforallL with X; apply landL2; reflexivity.
  Qed.

  Lemma landforallD {A} (f : A -> Frm) (P : Frm) {H : inhabited A} :
    (Forall a, f a) //\\ P -|- Forall a, (f a //\\ P).
  Proof.
  	split; [apply landforallDL | eapply landforallDR].
  Qed.

  Lemma lorforallDL {A} (f : A -> Frm) (P : Frm) :
    (Forall a, f a) \\// P |-- Forall a, (f a \\// P).
  Proof.
    apply lforallR; intro a; apply lorL.
    + apply lforallL with a; apply lorR1; reflexivity.
    + apply lorR2; reflexivity.
  Qed.

  Lemma limplTrue P : ltrue -->> P -|- P.
  Proof.
    split.
    + transitivity ((ltrue -->> P) //\\ ltrue).
      apply landR; [reflexivity | apply ltrueR].
      apply limplL; [apply ltrueR| apply landL1; reflexivity].
    + apply limplAdj; apply landL1; reflexivity.
  Qed.

  Lemma limplexistsE {T : Type} (P : T -> Frm) (Q : Frm) :
    (Exists x, P x) -->> Q -|- Forall x, (P x -->> Q).
  Proof.
    split.
    + apply lforallR; intro x. apply limplAdj; apply limplL.
      * apply lexistsR with x; reflexivity.
      * apply landL1; reflexivity.
    + apply limplAdj. rewrite landC, landexistsDL.
      apply lexistsL; intro x. rewrite landC, landforallDL.
      apply lforallL with x. apply limplL.
      * reflexivity.
      * apply landL1. reflexivity.
  Qed.

  Lemma limplforallER {T : Type} (P : T -> Frm) (Q : Frm) :
    Exists x, (P x -->> Q) |-- (Forall x, P x) -->> Q.
  Proof.
    apply lexistsL; intro x. apply limplAdj. apply limplL.
    + apply lforallL with x. reflexivity.
    + apply landL1. reflexivity.
  Qed.

  (* The following two lemmas have an explicit forall to help unification *)

  Lemma lforallR2 {T : Type} (P : Frm) (Q : T -> Frm) (H : P |-- lforall Q) :
  	forall x, P |-- Q x.
  Proof.
    intro x; rewrite H. apply lforallL with x; reflexivity.
  Qed.

  Lemma lexistsL2 {T : Type} (P : T -> Frm) (Q : Frm) (H : lexists P |-- Q) :
  	forall x, P x |-- Q.
  Proof.
    intro x; rewrite <- H. apply lexistsR with x; reflexivity.
  Qed.

  Lemma landtrueL : forall a, ltrue //\\ a -|- a.
  Proof.
    intros. split. eapply landL2. reflexivity. apply landR; eauto.
  Qed.

  Lemma landtrueR : forall a, a //\\ ltrue -|- a.
  Proof.
    intros. split. eapply landL1. reflexivity. apply landR; eauto.
  Qed.

  Lemma curry : forall a b c, (a //\\ b) -->> c -|- a -->> (b -->> c).
  Proof.
    clear - IL.
    intros.
    split.
    { eapply limplAdj.
      eapply limplAdj.
      rewrite landA.
      eapply landAdj.
      reflexivity. }
    { eapply limplAdj.
      rewrite <- landA.
      eapply landAdj.
      eapply landAdj. reflexivity. }
  Qed.

End ILogicFacts.
