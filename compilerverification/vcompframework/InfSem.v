Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import VCF.KnasterTarski.
Require Import VCF.GeneralDomain.
Require Import VCF.SetsDomain.

Record InfSem (A B: Type): Type := {
  fin_cases: A;
  inf_cases: B;
}.

Arguments fin_cases {_} {_} (_).
Arguments inf_cases {_} {_} (_).

Definition inf_sem_set_summary {A B} (fA: (A -> Prop) -> A) (fB: (B -> Prop) -> B) (ds: InfSem A B -> Prop): InfSem A B :=
{|
  fin_cases := fA (fun a => exists d, ds d /\ fin_cases d = a);
  inf_cases := fB (fun b => exists d, ds d /\ inf_cases d = b);
|}.

Definition inf_sem_fun2 {A B} (fA: A -> A -> A) (fB: B -> B -> B) (d1 d2: InfSem A B): InfSem A B :=
{|
  fin_cases := fA (fin_cases d1) (fin_cases d2);
  inf_cases := fB (inf_cases d1) (inf_cases d2);
|}.

Definition inf_sem_fun0 {A B} (fA: A) (fB: B): InfSem A B :=
{|
  fin_cases := fA;
  inf_cases := fB;
|}.

Definition inf_sem_rel {A B} (RA: A -> A -> Prop) (RB: B -> B -> Prop) (c1 c2: InfSem A B): Prop :=
    RA (fin_cases c1) (fin_cases c2) /\ RB (inf_cases c1) (inf_cases c2).

Lemma inf_sem_rel_iff: forall {A B} (RA: A -> A -> Prop) (RB: B -> B -> Prop),
  forall c1 c2,
    inf_sem_rel RA RB c1 c2 <->
    RA (fin_cases c1) (fin_cases c2) /\ RB (inf_cases c1) (inf_cases c2).
Proof.
  intros.
  split; intros [? ?]; [ | constructor]; auto.
Qed.

(* TODO: DELETE *)
Definition inf_sem_equiv {A B} {A_SETS: Sets.SETS A} {B_SETS: Sets.SETS B}: InfSem A B -> InfSem A B -> Prop  :=
  inf_sem_rel Sets.equiv Sets.equiv.

(* TODO: DELETE *)
Definition inf_sem_included {A B} {A_SETS: Sets.SETS A} {B_SETS: Sets.SETS B}: InfSem A B -> InfSem A B -> Prop :=
  inf_sem_rel Sets.included Sets.included.

Ltac simplify_InfSem_cases :=
  repeat
  match goal with
  | |- context [fin_cases (@Build_InfSem _ _ ?A ?B)] =>
    change (fin_cases (@Build_InfSem _ _ A B)) with A
  | |- context [inf_cases (@Build_InfSem _ _ ?A ?B)] =>
    change (inf_cases (@Build_InfSem _ _ A B)) with B
  | H: context [fin_cases (@Build_InfSem _ _ ?A ?B)] |- _ =>
    change (fin_cases (@Build_InfSem _ _ A B)) with A in H
  | H: context [inf_cases (@Build_InfSem _ _ ?A ?B)] |- _ =>
    change (inf_cases (@Build_InfSem _ _ A B)) with B in H
  end.

Lemma InfSem_Equiv
           {A B: Type}
           {RA: A -> A -> Prop}
           {RB: B -> B -> Prop}
           {EquA: Equivalence RA}
           {EquB: Equivalence RB}:
  Equivalence (inf_sem_rel RA RB).
Proof.
  constructor.
  + hnf; intros.
    constructor; reflexivity.
  + hnf; intros.
    destruct H; constructor; symmetry; auto.
  + hnf; intros.
    destruct H, H0; constructor; etransitivity; eauto.
Qed.

(* TODO direct prove inf_sem on A := sets B := sets *)

Lemma General_InfSem_CL
           {A B: Type}
           {RA RA': A -> A -> Prop}
           {RB RB': B -> B -> Prop}
           {lubA lubB}
           (CLA: CompleteLattice_Setoid RA RA' lubA)
           (CLB: CompleteLattice_Setoid RB RB' lubB):
  @CompleteLattice_Setoid
    (InfSem A B)
    (inf_sem_rel RA RB)
    (inf_sem_rel RA' RB')
    (inf_sem_set_summary lubA lubB).
Proof.
  refine (pair_CL fin_cases inf_cases _ _ _ CLA CLB _ _ _ _).
  + apply inf_sem_rel_iff; auto.
  + apply inf_sem_rel_iff; auto.
  + intros; split; reflexivity.
  + intros [? ?] [? ?]; simpl; intros; subst; auto.
Qed.

Lemma General_InfSem_union_proper
           {A B: Type}
           {RA: A -> A -> Prop}
           {RB: B -> B -> Prop}
           {unionA: A -> A -> A}
           {unionB: B -> B -> B}
           (PrA: Proper (RA ==> RA ==> RA) unionA)
           (PrB: Proper (RB ==> RB ==> RB) unionB):
  Proper (inf_sem_rel RA RB ==> inf_sem_rel RA RB ==> inf_sem_rel RA RB) (inf_sem_fun2 unionA unionB).
Proof.
  apply (pair_union_proper fin_cases inf_cases _ _ PrA PrB).
  + apply inf_sem_rel_iff; auto.
  + split; reflexivity.
  + intros [? ?] [? ?]; simpl; intros; subst; auto.
Qed.

(* TODO direct prove inf_sem on A := sets B := sets *)

Definition General_InfSem_CL_Domain
           (A B: Type)
           {CLA: CL_Domain A}
           {CLB: CL_Domain B}:
  CL_Domain (InfSem A B) :=
  Build_CL_Domain
    (InfSem A B)
    (inf_sem_rel Domain_R Domain_R)
    (inf_sem_rel Domain_R' Domain_R')
    (inf_sem_set_summary Domain_lub Domain_lub)
    ltac:(apply InfSem_Equiv; typeclasses eauto)
    ltac:(apply General_InfSem_CL; typeclasses eauto).

Definition General_InfSem_Union_Domain
           (A B: Type)
           {CLA: CL_Domain A}
           {CLB: CL_Domain B}
           {UnionA: Union_Domain A}
           {UnionB: Union_Domain B}:
  @Union_Domain (InfSem A B) (General_InfSem_CL_Domain A B) :=
  Build_Union_Domain
    (InfSem A B)
    (General_InfSem_CL_Domain A B)
    (inf_sem_fun2 Domain_union Domain_union)
    (inf_sem_fun0 Domain_empty Domain_empty)
    (General_InfSem_union_proper _ _).

Instance InfSem_CL_Domain
           (A B: Type)
           {_A_SETS: Sets.SETS A} {_B_SETS: Sets.SETS B}
           {_A_SETS_Properties: SETS_Properties A} {_B_SETS_Properties: SETS_Properties B}:
  CL_Domain (InfSem A B) :=
  @General_InfSem_CL_Domain A B SETS_included_CL_Domain SETS_flip_included_CL_Domain.

Instance InfSem_Union_Domain
           (A B: Type)
           {_A_SETS: Sets.SETS A} {_B_SETS: Sets.SETS B}
           {_A_SETS_Properties: SETS_Properties A} {_B_SETS_Properties: SETS_Properties B}:
  Union_Domain (InfSem A B) :=
  @General_InfSem_Union_Domain
    A B
    SETS_included_CL_Domain SETS_flip_included_CL_Domain
    SETS_included_Union_Domain SETS_flip_included_Union_Domain.
