Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import VCF.LiftConstructors.
Require Import VCF.PairConstructors.
Require Import VCF.KnasterTarski.

Class Union_Domain (A: Type) {CL_A: CL_Domain A} : Type := {
  Domain_union: A -> A -> A;
  Domain_empty: A;
  Domain_union_mono: Proper (Domain_R ==> Domain_R ==> Domain_R) Domain_union
}.

Class Concat_Domain (A: Type) {CL_A: CL_Domain A} : Type := {
  Domain_concat: A -> A -> A;
  Domain_concat_mono: forall a, Proper (Domain_R ==> Domain_R) (Domain_concat a)
}.

Existing Instances Domain_union_mono Domain_concat_mono.

Lemma lift_union_proper {X A R} {union: A -> A -> A} {Pr: Proper (R ==> R ==> R) union}:
  Proper (lift_rel2 R ==> lift_rel2 R ==> lift_rel2 R) (@lift_fun2 X A union).
Proof.
  hnf; intros; hnf; intros.
  intros a; unfold lift_fun2.
  apply Pr; auto.
Qed.

Lemma pair_union_proper
        {A B AB: Type}
        (projA: AB -> A)
        (projB: AB -> B)
        {RA: A -> A -> Prop}
        {RB: B -> B -> Prop}
        (RAB: AB -> AB -> Prop)
        {unionA: A -> A -> A}
        {unionB: B -> B -> B}
        (unionAB: AB -> AB -> AB)
        (PrA: Proper (RA ==> RA ==> RA) unionA)
        (PrB: Proper (RB ==> RB ==> RB) unionB):
  (forall c1 c2, RAB c1 c2 <-> RA (projA c1) (projA c2) /\ RB (projB c1) (projB c2)) ->
  (forall c1 c2, projA (unionAB c1 c2) = unionA (projA c1) (projA c2) /\
                 projB (unionAB c1 c2) = unionB (projB c1) (projB c2)) ->
  (forall c1 c2, projA c1 = projA c2 -> projB c1 = projB c2 -> c1 = c2) ->
  Proper (RAB ==> RAB ==> RAB) unionAB.
Proof.
  intros HR Hunion Hproj.
  unfold Proper, respectful.
  intros.
  rewrite HR in H, H0 |- *.
  rewrite !(proj1 (Hunion _ _)), !(proj2 (Hunion _ _)).
  split; [apply PrA | apply PrB]; tauto.
Qed.

Lemma prod_pair_union_proper
        {A B: Type}
        {RA: A -> A -> Prop}
        {RB: B -> B -> Prop}
        {unionA: A -> A -> A}
        {unionB: B -> B -> B}
        (PrA: Proper (RA ==> RA ==> RA) unionA)
        (PrB: Proper (RB ==> RB ==> RB) unionB):
  Proper (pair_rel2 RA RB ==> pair_rel2 RA RB ==> pair_rel2 RA RB) (pair_fun2 unionA unionB).
Proof.
  apply (pair_union_proper fst snd _ _ PrA PrB).
  + intros; reflexivity.
  + intros [? ?] [? ?]; simpl; intros; subst; split; reflexivity.
  + intros [? ?] [? ?]; simpl; intros; subst; reflexivity.
Qed.

Instance Lift_Union_Domain {A B} {CL_B: CL_Domain B} {Union_B: Union_Domain B}: Union_Domain (A -> B) :=
  Build_Union_Domain (A -> B) (Lift_CL_Domain A B) (lift_fun2 Domain_union) (lift_fun0 Domain_empty) (lift_union_proper).

Instance Pair_Union_Domain {A B}
         {CL_A: CL_Domain A} {CL_B: CL_Domain B}
         {Union_A: Union_Domain A} {Union_B: Union_Domain B}: Union_Domain (A * B) :=
  Build_Union_Domain
    (A * B) (Pair_CL_Domain _ _)
    (pair_fun2 Domain_union Domain_union)
    (pair_fun0 Domain_empty Domain_empty)
    (prod_pair_union_proper _ _).
