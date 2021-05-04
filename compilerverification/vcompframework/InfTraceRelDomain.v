Require Import Coq.Classes.Morphisms.
Require Import VCF.KnasterTarski.
Require Import VCF.TraceGeneral.
Require Import VCF.InfSem.
Require Import VCF.SetsDomain.
Require Import VCF.FinTraceRelDomain.

Module iTrRel.

Definition concat
             {A B C finT infT}
             {finTr: Trace.FinTrace finT}
             {infTr: Trace.InfTrace finT infT}
             (d1: InfSem (A -> finT -> B -> Prop) (A -> infT -> Prop))
             (d2: InfSem (B -> finT -> C -> Prop) (B -> infT -> Prop)):
  InfSem (A -> finT -> C -> Prop) (A -> infT -> Prop) :=
{|
  fin_cases := TrRel.concat (fin_cases d1) (fin_cases d2);
  inf_cases := Sets.union (TrRel.dia (fin_cases d1) (inf_cases d2)) (inf_cases d1);
|}.

Definition id
             {A finT infT}
             {finTr: Trace.FinTrace finT}
             {infTr: Trace.InfTrace finT infT}
  : InfSem (A -> finT -> A -> Prop) (A -> infT -> Prop) :=
{|
  fin_cases := TrRel.id;
  inf_cases := Sets.empty;
|}.

Definition test
             {A finT infT}
             {finTr: Trace.FinTrace finT}
             {infTr: Trace.InfTrace finT infT}
             (X: A -> Prop) (tr0: finT)
  : InfSem (A -> finT -> A -> Prop) (A -> infT -> Prop) :=
{|
  fin_cases := TrRel.test X tr0;
  inf_cases := Sets.empty;
|}.

End iTrRel.

Lemma iTrRel_test_congr {A finT infT}
             {finTr: Trace.FinTrace finT}
             {infTr: Trace.InfTrace finT infT}:
  Proper (Sets.equiv ==> eq ==> Domain_R') (@iTrRel.test A finT infT _ _).
Proof.
  unfold Proper, respectful, iTrRel.test; unfold_SETS_tac no_extra_simplify.
  intros; constructor.
  + apply TrRel_test_congr; auto.
  + reflexivity.
Qed.

Lemma iTrRel_concat_congr {A B C finT infT}
             {finTr: Trace.FinTrace finT}
             {infTr: Trace.InfTrace finT infT}:
  Proper (Domain_R' ==> Domain_R' ==> Domain_R') (@iTrRel.concat A B C finT infT _ _).
Proof.
  unfold Proper, respectful, iTrRel.concat.
  intros.
  destruct H as [?H ?H], H0 as [?H ?H].
  constructor.
  + apply TrRel_concat_congr; auto.
  + apply Sets_union_congr; [apply TrRel_dia_congr |]; auto.
Qed.

Lemma iTrRel_concat_mono {A B C finT infT}
             {finTr: Trace.FinTrace finT}
             {infTr: Trace.InfTrace finT infT} a:
  Proper (Domain_R ==> Domain_R) (@iTrRel.concat A B C finT infT _ _ a).
Proof.
  unfold Proper, respectful, iTrRel.concat.
  intros.
  destruct H as [?H ?H].
  constructor.
  + apply TrRel_concat_mono; auto.
    reflexivity.
  + apply Sets_union_mono; [apply TrRel_dia_mono |]; auto;
    reflexivity.
Qed.

Lemma iTrRel_concat_id: forall  {A B finT infT}
             {finTr: Trace.FinTrace finT}
             {infTr: Trace.InfTrace finT infT}
             (r: InfSem (A -> finT -> B -> Prop) (A -> infT -> Prop)),
  Domain_R' (iTrRel.concat r iTrRel.id) r.
Proof.
  intros.
  constructor.
  + apply TrRel_concat_id.
  + rewrite <- (empty_union (inf_cases r)).
    apply Sets_union_congr; [| reflexivity].
    apply TrRel_dia_empty.
Qed.

Existing Instances iTrRel_test_congr
                   iTrRel_concat_congr
                   iTrRel_concat_mono.

