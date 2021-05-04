Require Import VCF.BoubakiWitt.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import Equivalence.
Require Import Morphisms.
Require Import Classical.
Require Import List.
Require Import Psatz.

Module Rel.

Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

Definition concat {A B C: Type} (r1: A -> B -> Prop) (r2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, r1 a b /\ r2 b c.

Definition filter1 {A B: Type} (f: A -> Prop): A -> B -> Prop :=
  fun a b => f a.

Definition filter2 {A B: Type} (f: B -> Prop): A -> B -> Prop :=
  fun a b => f b.

Definition test {A} (X: A -> Prop): A -> A -> Prop :=
  fun st1 st2 => st1 = st2 /\ X st1.

Definition dia {A B: Type} (X: A -> B -> Prop) (Y: B -> Prop): A -> Prop :=
  fun a => exists b, X a b /\ Y b.

End Rel.

Lemma Rel_test_congr A:
  Proper (Sets.equiv ==> Sets.equiv) (@Rel.test A).
Proof.
  unfold Proper, respectful, Rel.test; unfold_SETS_tac no_extra_simplify.
  intros X Y ?.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Rel_concat_congr {A B C}:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@Rel.concat A B C).
Proof.
  unfold Proper, respectful, Rel.concat; unfold_SETS_tac no_extra_simplify.
  intros X1 X2 ? Y1 Y2 ?.
  intros a c.
  unfold iff.
  split.
  + intros [b [? ?]].
    exists b.
    rewrite <- H, <- H0.
    tauto.
  + intros [b [? ?]].
    exists b.
    rewrite H, H0.
    tauto.
Qed.

Lemma Rel_dia_congr A B:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@Rel.dia A B).
Proof.
  unfold Proper, respectful, Rel.dia; unfold_SETS_tac no_extra_simplify.
  intros.
  apply Morphisms_Prop.ex_iff_morphism; intros ?.
  rewrite H, H0.
  tauto.
Qed.

Lemma Rel_concat_mono {A B C}:
  Proper (Sets.included ==> Sets.included ==> Sets.included) (@Rel.concat A B C).
Proof.
  unfold Proper, respectful, Rel.concat; unfold_SETS_tac no_extra_simplify.
  intros X1 X2 ? Y1 Y2 ?.
  intros a c [b [? ?]].
  exists b.
  auto.
Qed.

Lemma Rel_dia_mono A B:
  Proper (Sets.included ==> Sets.included ==> Sets.included) (@Rel.dia A B).
Proof.
  unfold Proper, respectful, Rel.dia; unfold_SETS_tac no_extra_simplify.
  intros.
  destruct H1 as [b [? ?]]; exists b.
  auto.
Qed.

Lemma Rel_concat_id: forall A B (r: A -> B -> Prop),
  Sets.equiv (Rel.concat r Rel.id) r.
Proof.
  intros.
  unfold Rel.concat, Rel.id; unfold_SETS_tac no_extra_simplify.
  intros.
  split; intros.
  + destruct H as [? [? ?]].
    subst.
    auto.
  + exists a0; auto.
Qed.

Lemma Rel_dia_empty: forall A B (r: A -> B -> Prop),
  Sets.equiv (Rel.dia r Sets.empty) Sets.empty.
Proof.
  intros.
  unfold Rel.dia; unfold_SETS_tac no_extra_simplify.
  intros.
  split; intros.
  + destruct H as [? [? ?]].
    tauto.
  + tauto.
Qed.

Existing Instances Rel_test_congr
                   Rel_concat_congr
                   Rel_dia_congr
                   Rel_concat_mono
                   Rel_dia_mono.

Lemma fold_right_concat_iff: forall A rs r (x z: A),
  fold_right Rel.concat r rs x z ->
  exists y, fold_right Rel.concat Rel.id rs x y /\ r y z.
Proof.
  intros.
  revert x z H; induction rs; intros; simpl in H |- *.
  + exists x; split; auto.
    unfold Rel.id; auto.
  + destruct H as [a' [? ?]].
    apply IHrs in H0.
    destruct H0 as [y [? ?]].
    exists y; split.
    - exists a'; auto.
    - auto.
Qed.

Ltac BinRel_solve_mono :=
  idtac;
  match goal with
  | |- Sets.included (Rel.concat _ _) (Rel.concat _ _) =>
         refine (Rel_concat_mono _ _ _ _ _ _); solve_mono BinRel_solve_mono
  | |- _ => idtac
  end.

