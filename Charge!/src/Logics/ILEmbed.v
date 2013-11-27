Require Import Setoid.
Require Import Morphisms.
Require Import RelationClasses.
Require Import Logics.ILogic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section ILogicEmbed.
  Context {A} `{ILOpsA: ILogicOps A}.
  Context {B} `{ILOpsB: ILogicOps B}.

  Class EmbedOp := { embed : A -> B }.

  Class Embed {EmbOp: EmbedOp} := {
     embed_sound p q : p |-- q -> embed p |-- embed q;

     embedlforall T f : Forall x : T, embed (f x) -|- embed (Forall x : T, f x);
     embedlexists T f : Exists x : T, embed (f x) -|- embed (Exists x : T, f x);
     embedImpl a b : (embed a) -->> (embed b) -|- embed (a -->> b)
  }.
End ILogicEmbed.

Implicit Arguments EmbedOp [].
Implicit Arguments Embed [[ILOpsA] [ILOpsB] [EmbOp]].

Section ILogicEmbedOps.
  Context {A B} `{HAB: Embed A B} {ILA: ILogic A} {ILB: ILogic B}.

  Definition lembedand (a : A) (b : B) := (embed a) //\\ b.
  Definition lembedimpl (a : A) (b : B) := (embed a) -->> b.

End ILogicEmbedOps.


Section ILEmbedId.

	Context {A : Type} `{ILA : ILogic A}.

	Instance EmbedOpId : EmbedOp A A := { embed := id }.
	Instance EmbedId : Embed A A.
	Proof.
		split; firstorder.
	Qed.

End ILEmbedId.

Section ILogicEmbedCompose.
  Context {A B} `{HAB: Embed A B} {ILA: ILogic A} {ILB: ILogic B}.
  Context {C} {HC: ILogicOps C} {HE: EmbedOp B C} {HBC : Embed B C} {ILC: ILogic C}.

  Instance embedOpCompose : EmbedOp A C := { embed := fun x => embed (embed x) }.

  Program Instance embedCompose : Embed A C.
  Next Obligation.
  	do 2 apply embed_sound; assumption.
  Qed.
  Next Obligation.
  	split;
  	rewrite embedlforall; apply embed_sound; rewrite embedlforall; reflexivity.
  Qed.
  Next Obligation.
  	split;
  	rewrite embedlexists; apply embed_sound; rewrite embedlexists; reflexivity.
  Qed.
  Next Obligation.
  	split;
  	rewrite embedImpl; apply embed_sound; rewrite embedImpl; reflexivity.
  Qed.

End ILogicEmbedCompose.

Infix "/\\" := lembedand (at level 75, right associativity).
Infix "->>" := lembedimpl (at level 77, right associativity).

Section ILogicEmbedFacts.
  Context {A B} `{HAB: Embed A B} {ILA: ILogic A} {ILB: ILogic B}.

  Global Instance embed_lentails_m :
    Proper (lentails ==> lentails) embed.
  Proof.
    intros a b Hab; apply embed_sound; assumption.
  Qed.

  Global Instance embed_lequiv_m :
    Proper (lequiv ==> lequiv) embed.
  Proof.
    intros a b Hab; split; destruct Hab; apply embed_sound; assumption.
  Qed.

  Global Instance lembedimpl_lentails_m:
    Proper (lentails --> lentails ++> lentails) lembedimpl.
  Proof.
    intros P P' HP Q Q' HQ; red in HP.
    unfold lembedimpl. rewrite <- HP, HQ; reflexivity.
  Qed.

  Global Instance lembedimpl_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lembedimpl.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lembedimpl_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lembedand_lentails_m:
    Proper (lentails ==> lentails ==> lentails) lembedand.
  Proof.
    intros P P' HP Q Q' HQ.
    unfold lembedand. rewrite HP, HQ. reflexivity.
  Qed.

  Global Instance lembedand_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lembedand.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lembedand_lentails_m; (apply HP || apply HQ).
  Qed.

  Lemma embedland a b : embed a //\\ embed b -|- embed (a //\\ b).
  Proof.
    do 2 rewrite land_is_forall; rewrite <- embedlforall; split;
    apply lforallR; intro x; apply lforallL with x;
    destruct x; reflexivity.
  Qed.

  Lemma embedlor a b : embed a \\// embed b -|- embed (a \\// b).
  Proof.
    do 2 rewrite lor_is_exists; erewrite <- embedlexists; split;
    apply lexistsL; intro x; apply lexistsR with x;
    destruct x; reflexivity.
  Qed.

  Lemma embedlfalse : embed lfalse -|- lfalse.
  Proof.
    rewrite lfalse_is_exists; erewrite <- embedlexists; split;
    [apply lexistsL; intro x; destruct x | apply lfalseL].
  Qed.

  Lemma embedltrue : embed ltrue -|- ltrue.
  Proof.
    rewrite ltrue_is_forall; rewrite <- embedlforall; split;
    [apply ltrueR | apply lforallR; intro x; destruct x].
  Qed.

  Lemma embedlandC (P R : B) (Q : A) : P //\\ Q /\\ R -|- Q /\\ P //\\ R.
  Proof.
  	unfold lembedand; rewrite <- landA, (landC P), landA; reflexivity.
  Qed.

  Lemma embedlimplC (P R : B) (Q : A) : P -->> Q ->> R -|- Q ->> P -->> R.
  Proof.
    unfold lembedimpl. do 2 rewrite limplAdj2.
    rewrite landC. reflexivity.
  Qed.

  Lemma limpllandC (P Q R : B) : P //\\ (Q -->> R) |-- Q -->> P //\\ R.
  Proof.
  	apply limplAdj; rewrite landA; apply landR.
  	+ apply landL1. reflexivity.
  	+ apply landL2. apply limplL; [reflexivity | apply landL1; reflexivity].
  Qed.

  Lemma embed_existsL (P : A) : Exists x : |-- P, ltrue |-- embed P.
  Proof.
  	apply lexistsL; intro H.
  	rewrite <- H. rewrite embedltrue. apply ltrueR.
  Qed.

End ILogicEmbedFacts.
