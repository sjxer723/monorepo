Require Import Coq.Classes.Morphisms.
Require Import VCF.TraceGeneral.
Require Import VCF.SetsDomain.

Module TrRel.

Definition concat {A B C T} {finTr: Trace.FinTrace T} (r1: A -> T -> B -> Prop) (r2: B -> T -> C -> Prop): A -> T -> C -> Prop :=
  fun a tr c =>
    exists b tr1 tr2, r1 a tr1 b /\ r2 b tr2 c /\ tr = Trace.fin_concat tr1 tr2.

Definition id {A T} {finTr: Trace.FinTrace T}: A -> T -> A -> Prop :=
  fun a1 tr a2 => a1 = a2 /\ tr = Trace.empty.

Definition test {A T} {finTr: Trace.FinTrace T} (X: A -> Prop) (tr0: T): A -> T -> A -> Prop :=
  fun a1 tr a2 => a1 = a2 /\ X a1 /\ tr = tr0.

Definition dia {A B finT infT} {finTr: Trace.FinTrace finT} {infTr: Trace.InfTrace finT infT} (r: A -> finT -> B -> Prop) (X: B -> infT -> Prop): A -> infT -> Prop :=
  fun a tr =>
    exists b tr1 tr2, r a tr1 b /\ X b tr2 /\ tr = Trace.inf_concat tr1 tr2.

End TrRel.

Lemma TrRel_test_congr A T {finTr: Trace.FinTrace T}:
  Proper (Sets.equiv ==> eq ==> Sets.equiv) (@TrRel.test A T _).
Proof.
  unfold Proper, respectful, TrRel.test; unfold_SETS_tac no_extra_simplify.
  intros X Y ?.
  intros.
  subst.
  rewrite H.
  reflexivity.
Qed.

Lemma TrRel_concat_congr {A B C T} {finTr: Trace.FinTrace T}:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@TrRel.concat A B C T _).
Proof.
  unfold Proper, respectful, TrRel.concat; unfold_SETS_tac no_extra_simplify.
  intros X1 X2 ? Y1 Y2 ?.
  intros a c.
  unfold iff.
  split.
  + intros [b [tr1 [tr2 [? [? ?]]]]].
    exists b, tr1, tr2.
    rewrite <- H, <- H0.
    tauto.
  + intros [b [tr1 [tr2 [? [? ?]]]]].
    exists b, tr1, tr2.
    rewrite H, H0.
    tauto.
Qed.

Lemma TrRel_dia_congr {A B finT infT} {finTr: Trace.FinTrace finT} {infTr: Trace.InfTrace finT infT}:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@TrRel.dia A B finT infT _ _).
Proof.
  unfold Proper, respectful, TrRel.dia; unfold_SETS_tac no_extra_simplify.
  intros.
  apply Morphisms_Prop.ex_iff_morphism; intros ?.
  apply Morphisms_Prop.ex_iff_morphism; intros ?.
  apply Morphisms_Prop.ex_iff_morphism; intros ?.
  rewrite H, H0.
  tauto.
Qed.

Lemma TrRel_concat_mono {A B C T} {finTr: Trace.FinTrace T}:
  Proper (Sets.included ==> Sets.included ==> Sets.included) (@TrRel.concat A B C T _).
Proof.
  unfold Proper, respectful, TrRel.concat; unfold_SETS_tac no_extra_simplify.
  intros X1 X2 ? Y1 Y2 ?.
  intros a t c [b [tr1 [tr2 [? [? ?]]]]].
  exists b, tr1, tr2.
  auto.
Qed.

Lemma TrRel_dia_mono {A B finT infT} {finTr: Trace.FinTrace finT} {infTr: Trace.InfTrace finT infT}:
  Proper (Sets.included ==> Sets.included ==> Sets.included) (@TrRel.dia A B finT infT _ _).
Proof.
  unfold Proper, respectful, TrRel.dia; unfold_SETS_tac no_extra_simplify.
  intros.
  destruct H1 as [b [tr1 [tr2 [? [? ?]]]]]; exists b, tr1, tr2.
  auto.
Qed.

Lemma TrRel_concat_id: forall {A B T} {finTr: Trace.FinTrace T} (r: A -> T -> B -> Prop),
  Sets.equiv (TrRel.concat r TrRel.id) r.
Proof.
  intros.
  unfold TrRel.concat, TrRel.id; unfold_SETS_tac no_extra_simplify.
  intros.
  split; intros.
  + destruct H as [b [tr1 [tr2 [? [[? ?] ?]]]]].
    subst.
    rewrite Trace.fin_concat_empty.
    auto.
  + exists a1, a0, Trace.empty.
    rewrite Trace.fin_concat_empty.
    auto.
Qed.

Lemma TrRel_dia_empty: forall {A B finT infT} {finTr: Trace.FinTrace finT} {infTr: Trace.InfTrace finT infT} (r: A -> finT -> B -> Prop),
  Sets.equiv (TrRel.dia r Sets.empty) Sets.empty.
Proof.
  intros.
  unfold TrRel.dia; unfold_SETS_tac no_extra_simplify.
  intros.
  split; intros.
  + destruct H as [? [? [? ?]]].
    tauto.
  + tauto.
Qed.

Existing Instances TrRel_test_congr
                   TrRel_concat_congr
                   TrRel_dia_congr
                   TrRel_concat_mono
                   TrRel_dia_mono.
