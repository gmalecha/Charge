Require Import Setoid Morphisms RelationClasses OrderedType.
Require Import String.

Class DecidableEq (A : Type) := { dec_eq (a b : A) : {a = b} + {a <> b} }.

Instance DecNat : DecidableEq nat. Proof. split. decide equality. Qed.
Instance DecString : DecidableEq string. Proof. split. repeat (decide equality). Qed.
Instance DecEqPair (X Y : Type) {HX : DecidableEq X} {HY : DecidableEq Y} :
  DecidableEq (X * Y).
Proof. 
  split; destruct HX, HY; decide equality. 
Qed.

Definition EquivPreorder {A : Type} {ord : relation A} {Heq : Equivalence ord} : PreOrder ord.
Proof.
  firstorder.
Qed.

Class Rel (A : Type) := rel : relation A.
(*
Infix "===" := equiv (at level 70, no associativity).

Instance Equiv_eq {A : Type} : Equiv A | 100 := eq.
*)
Instance Equiv_option {A} {Heq: Rel A} : Rel (option A) | 0 := {
    rel := fun a b => 
               (a = None /\ b = None) \/
               (exists x y, a = Some x /\ b = Some y /\ rel x y)
}.

Instance Equiv_unit: Rel unit | 0 := fun _ _ => True.

Instance Equivalence_unit : Equivalence (@rel unit _).
Proof. firstorder. Qed.

Section EquivProducts.
  Context {A B : Type} `{eA : Rel A} `{eB : Rel B}.
  Context {HA: Equivalence (@rel _ eA)}.
  Context {HB: Equivalence (@rel _ eB)}.

  Global Instance Rel_prod : Rel (A * B) :=
    fun p1 p2 => (rel (fst p1) (fst p2) /\ rel (snd p1) (snd p2)).

  Global Instance prod_proper : Proper (rel ==> rel ==> rel) (@pair A B).
  Proof.
    intros a a' Ha b b' Hb; split; assumption.
  Qed.

  Global Instance equiv_prod : Equivalence rel.
  Proof.
    split.
      intros [a b]; split; reflexivity.
      intros [a1 b1] [a2 b2] [Ha Hb]; split; symmetry; assumption.
    intros [a1 b1] [a2 b2] [a3 b3] [Ha12 Hb12] [Ha23 Hb23];
      split; etransitivity; eassumption.
  Qed.

End EquivProducts.

