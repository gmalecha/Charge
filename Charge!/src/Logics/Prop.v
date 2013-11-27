Require Import Relations.
Require Import RelationClasses.
Require Import Logics.ILogic.

Set Implicit Arguments.
Set Strict Implicit.

(* Prop is an intuitionistic logic *)
Global Instance ILogicOps_Prop : ILogicOps Prop :=
{|
  lentails P Q := P -> Q;
  ltrue        := True;
  lfalse       := False;
  limpl    P Q := P -> Q;
  land     P Q := P /\ Q;
  lor      P Q := P \/ Q;
  lforall  T F := forall x:T, F x;
  lexists  T F := exists x:T, F x
|}.

Global Instance ILogic_Prop : ILogic Prop.
Proof.
  split; cbv; firstorder.
Qed.

(* Make the setoid system realize that these are the same things (in the
   direction that seems useful. *)
Instance: subrelation lentails Basics.impl.
Proof. reflexivity. Qed.
Instance: subrelation lequiv iff.
Proof. reflexivity. Qed.

Section EmbedProp.
  Require Import Logics.ILEmbed.

  Context {A : Type} `{HIL: ILogic A} {HPropOp: EmbedOp Prop A} {HProp: Embed Prop A}.

  Lemma embedPropExists (p : Prop) : embed p |-- Exists x : p, ltrue.
  Proof.
    assert (p |-- Exists x : p, (|-- ltrue)). {
      intros Hp. exists Hp. apply ltrueR.
    } etransitivity.
    rewrite H. reflexivity.
    rewrite <- embedlexists. apply lexistsL. intros Hp.
    apply lexistsR with Hp. apply ltrueR.
  Qed.

  Lemma embedPropExistsL (p : Prop) (P : A) : Exists x : p, P |-- embed p.
  Proof.
    assert (Exists x : p, ltrue |-- p). {
      intros HP. destruct HP as [HP _]. apply HP.
    }
    etransitivity; [|rewrite <- H]; [reflexivity|].
    rewrite <- embedlexists. apply lexistsL; intro Hp.
    apply lexistsR with Hp. rewrite embedltrue. apply ltrueR.
  Qed.

  (* TODO rename embedPropExists to embedPropExistsR *)
  Lemma embedPropExists' (p : Prop) : Exists x : p, ltrue -|- embed p.
  Proof.
        split; [apply embedPropExistsL | apply embedPropExists].
  Qed.

  Lemma embedPropL (p : Prop) C (H: p -> |-- C) :
    embed p |-- C.
  Proof.
        rewrite embedPropExists.
        apply lexistsL; intro Hp.
        apply H; apply Hp.
  Qed.

  Lemma embedPropR (p : Prop) (P : A) (H : p) : P |-- embed p.
  Proof.
    assert (ltrue |-- p) by (intros _; assumption).
    rewrite <- H0, embedltrue; apply ltrueR.
  Qed.

  Lemma lpropandL (p: Prop) Q C (H: p -> Q |-- C) :
    p /\\ Q |-- C.
  Proof.
    unfold lembedand.
    apply landAdj.
    apply embedPropL.
    intros Hp.
    apply limplAdj.
    apply landL2.
    apply H. assumption.
  Qed.

  Lemma lpropandR C (p: Prop) Q (Hp: p) (HQ: C |-- Q) :
    C |-- p /\\ Q.
  Proof.
    unfold lembedand.
    apply landR; [|assumption].
    rewrite <- embedPropR. apply ltrueR. assumption.
  Qed.

  Lemma lpropimplL (p: Prop) (Q C: A) (Hp: p) (HQ: Q |-- C) :
    p ->> Q |-- C.
  Proof.
    unfold lembedimpl.
    rewrite <- embedPropR, limplTrue; assumption.
  Qed.

  Lemma lpropimplR C (p: Prop) Q (H: p -> C |-- Q) :
    C |-- p ->> Q.
  Proof.
    unfold lembedimpl.
    apply limplAdj. rewrite landC. apply lpropandL. assumption.
  Qed.

  (* Derivable but useful *)
  Lemma lpropandTrue P : True /\\ P -|- P.
  Proof.
    split.
    + apply lpropandL; intros _; reflexivity.
    + apply landR.
      * replace True with (@ltrue Prop _) by reflexivity.
        rewrite embedltrue. apply ltrueR.
      * reflexivity.
  Qed.

  Lemma lpropandFalse P : False /\\ P -|- lfalse.
  Proof.
    split.
    + apply lpropandL; intros H; destruct H.
    + apply lfalseL.
  Qed.

End EmbedProp.
