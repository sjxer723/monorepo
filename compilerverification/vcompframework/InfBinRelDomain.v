Require Import Morphisms.
Require Import VCF.KnasterTarski.
Require Import VCF.GeneralDomain.
Require Import VCF.SetsDomain.
Require Import VCF.BinRelDomain.
Require Import VCF.InfSem.

Module iRel.

Definition concat {A B C: Type} (r1: InfSem (A -> B -> Prop) (A -> Prop)) (r2: InfSem (B -> C -> Prop) (B -> Prop)): InfSem (A -> C -> Prop) (A -> Prop) :=
{|
  fin_cases := Rel.concat (fin_cases r1) (fin_cases r2);
  inf_cases := Sets.union (Rel.dia (fin_cases r1) (inf_cases r2)) (inf_cases r1)
|}.

Definition id {A: Type}: InfSem (A -> A -> Prop) (A -> Prop) :=
{|
  fin_cases := Rel.id;
  inf_cases := Sets.empty;
|}.

Definition test {A} (X: A -> Prop): InfSem (A -> A -> Prop) (A -> Prop) :=
{|
  fin_cases := Rel.test X;
  inf_cases := Sets.empty;
|}.

Definition dia {A B: Type} (X: InfSem (A -> B -> Prop) (A -> Prop)) (Y: B -> Prop): A -> Prop :=
  Rel.dia (fin_cases X) Y.

End iRel.

Lemma iRel_test_congr A:
  Proper (Sets.equiv ==> Domain_R') (@iRel.test A).
Proof.
  unfold Proper, respectful, iRel.test.
  intros; constructor.
  + apply Rel_test_congr; auto.
  + reflexivity.
Qed.

Lemma iRel_concat_congr {A B C}:
  Proper (Domain_R' ==> Domain_R' ==> Domain_R') (@iRel.concat A B C).
Proof.
  unfold Proper, respectful, iRel.concat.
  intros.
  destruct H as [?H ?H], H0 as [?H ?H].
  constructor.
  + apply Rel_concat_congr; auto.
  + apply Sets_union_congr; [apply Rel_dia_congr |]; auto.
Qed.

Lemma iRel_concat_mono {A B C} a:
  Proper (Domain_R ==> Domain_R) (@iRel.concat A B C a).
Proof.
  unfold Proper, respectful, iRel.concat.
  intros.
  destruct H as [?H ?H].
  constructor.
  + apply Rel_concat_mono; auto.
    reflexivity.
  + apply Sets_union_mono; [apply Rel_dia_mono |]; auto;
    reflexivity.
Qed.

Lemma iRel_concat_id: forall A B (r: InfSem (A -> B -> Prop) (A -> Prop)),
  Domain_R' (iRel.concat r iRel.id) r.
Proof.
  intros.
  constructor.
  + apply Rel_concat_id.
  + rewrite <- (empty_union (inf_cases r)).
    apply Sets_union_congr; [| reflexivity].
    apply Rel_dia_empty.
Qed.

(* TODO DELETE, because they will not be used at top level *)

Existing Instances iRel_test_congr
                   iRel_concat_congr
                   iRel_concat_mono.

