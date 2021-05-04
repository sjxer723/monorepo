Require Import ZArith.
Require Import Equivalence.
Require Import Morphisms.

Module ZFunc.

Local Open Scope Z.

Definition add {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a + g a.

Definition sub {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a - g a.

Definition mul {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a * g a.

Definition test_eq {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a = g a.

Definition test_le {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a <= g a.

Definition equiv {A: Type} (f g: A -> Z): Prop :=
  forall a, f a = g a.

Definition le {A: Type} (f g: A -> Z): Prop :=
  forall a, f a <= g a.

End ZFunc.


Declare Scope func_scop.
Delimit Scope func_scope with Func.

Notation "f + g" := (ZFunc.add f g): func_scope.
Notation "f - g" := (ZFunc.sub f g): func_scope.
Notation "f * g" := (ZFunc.mul f g): func_scope.

Lemma Func_equiv_refl: forall A, Reflexive (@ZFunc.equiv A).
Proof.
  intros.
  unfold Reflexive.
  unfold ZFunc.equiv.
  intros.
  reflexivity.
Qed.

Lemma Func_equiv_sym: forall A, Symmetric (@ZFunc.equiv A).
Proof.
  intros.
  unfold Symmetric.
  unfold ZFunc.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Func_equiv_trans: forall A, Transitive (@ZFunc.equiv A).
Proof.
  intros.
  unfold Transitive.
  unfold ZFunc.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_add_equiv: forall A,
  Proper (@ZFunc.equiv A ==> @ZFunc.equiv A ==> @ZFunc.equiv A) ZFunc.add.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold ZFunc.equiv in H.
  unfold ZFunc.equiv in H0.
  unfold ZFunc.equiv.
  intros.
  unfold ZFunc.add.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_sub_equiv: forall A,
  Proper (@ZFunc.equiv A ==> @ZFunc.equiv A ==> @ZFunc.equiv A) ZFunc.sub.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold ZFunc.equiv in H.
  unfold ZFunc.equiv in H0.
  unfold ZFunc.equiv.
  intros.
  unfold ZFunc.sub.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_mul_equiv: forall A,
  Proper (@ZFunc.equiv A ==> @ZFunc.equiv A ==> @ZFunc.equiv A) ZFunc.mul.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold ZFunc.equiv in H.
  unfold ZFunc.equiv in H0.
  unfold ZFunc.equiv.
  intros.
  unfold ZFunc.mul.
  rewrite H, H0.
  reflexivity.
Qed.

Existing Instances Func_equiv_refl
                   Func_equiv_sym
                   Func_equiv_trans
                   Func_add_equiv
                   Func_sub_equiv
                   Func_mul_equiv.

