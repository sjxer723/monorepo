Require Import ClassicalFacts.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationPairs.
Require Import VCF.LiftConstructors.
Require Import VCF.PairConstructors.

Class AntiSymmetric_Setoid {A:Type} (R: A-> A-> Prop) (R':A->A->Prop): Prop :=
  antisymmetricity_setoid: forall a b, R a b -> R b a -> R' a b. 
(*反对称性*)

Class PartialOrder_Setoid {A:Type} (R: A-> A-> Prop)(R':A->A->Prop): Prop :=
{
  PO_AntiSymmetric_Setoid: AntiSymmetric_Setoid R R';
  PO_Reflexive_Setoid: forall x y, R' x y -> R x y;
  PO_Transitive: Transitive R
}.
(*偏序关系*)

Existing Instances PO_AntiSymmetric_Setoid PO_Transitive.

Instance PartialOrder_Setoid_Reflexive:forall A:Type, forall R R':A->A->Prop,
  Equivalence R' -> PartialOrder_Setoid R R' -> Reflexive R.
Proof.
  intros.
  hnf; intros.
  apply PO_Reflexive_Setoid.
  reflexivity.
Qed.

Instance PartialOrder_Setoid_Proper {A:Type} (R R': A -> A -> Prop) {equ: Equivalence R'} {PO: PartialOrder_Setoid R R'}: Proper (R' ==> R' ==> iff) R.
Proof.
  unfold Proper, respectful.
  intros.
  split; intros.
  + transitivity x0; [| apply PO_Reflexive_Setoid; auto].
    transitivity x; [apply PO_Reflexive_Setoid; symmetry; auto |].
    auto.
  + transitivity y0; [| apply PO_Reflexive_Setoid; symmetry; auto].
    transitivity y; [apply PO_Reflexive_Setoid; auto |].
    auto.
Qed.

Definition upper_bound {A:Type} (R:A->A->Prop) (T: A -> Prop) (bnd:A):Prop :=
forall a, T a -> R a bnd.
(*检查bnd是否是一个集合的上界*)

Definition least_upper_bound {A:Type} (R:A->A->Prop) (T: A -> Prop) (bnd:A): Prop :=
  upper_bound R T bnd /\
  forall bnd', upper_bound R T bnd' -> R bnd bnd'.
(*一个集合的上确界*)

Definition lower_bound {A:Type} (R:A->A->Prop) (T: A -> Prop) (bnd:A):Prop :=
forall a, T a -> R bnd a.
(*检查bnd是否是一个集合的下界*)

Definition greatest_lower_bound {A:Type} (R:A->A->Prop) (T: A -> Prop) (bnd:A): Prop :=
  lower_bound R T bnd /\
  forall bnd', lower_bound R T bnd' -> R bnd' bnd.
(*一个集合的下确界*)

Class CompleteLattice_Setoid {A:Type} (R:A->A->Prop) (R': A-> A-> Prop) (lub: (A -> Prop) -> A): Prop :=
{
  CL_PartialOrder: PartialOrder_Setoid R R';
  CL_Complete_lub: forall T, least_upper_bound R T (lub T);
  lub_congr: forall T1 T2, (forall a, T1 a <-> T2 a) -> R' (lub T1) (lub T2);
}.

Existing Instance CL_PartialOrder.

Definition fixpoint {A:Type} (f:A->A) (a:A)(R':A->A->Prop): Prop:=
R' a (f a).
(* 函数f的不动点, R' 为等价关系*)

Definition least_fixpoint {A:Type} (f:A->A) (R:A->A->Prop) (R':A->A->Prop)(a:A): Prop:=
fixpoint f a R' /\ forall a', fixpoint f a' R'-> R a a'.
(* 最小不动点 *)

Definition greatest_fixpoint {A:Type} (f:A->A) (R:A->A->Prop) (R':A->A->Prop)(a:A): Prop:=
fixpoint f a R' /\ forall a', fixpoint f a' R'-> R a' a.
(* 最大不动点 *)

Definition lower_than_fp {A:Type} (F:A->A) (R:A->A->Prop): A -> Prop :=
  fun x => R x (F x).

Definition greater_than_fp {A:Type} (F:A->A) (R:A->A->Prop): A -> Prop :=
  fun x => R (F x) x.

Definition glb_of_lub {A:Type} (R:A->A->Prop) (lub: (A -> Prop) -> A): (A -> Prop) -> A :=
  fun X => lub (lower_bound R X).

Definition KT_fix_g {A: Type} {R R': A -> A -> Prop} {lub} {CL: CompleteLattice_Setoid R R' lub} (f: A -> A): A :=
  lub (lower_than_fp f R).

Definition KT_fix_l {A: Type} {R R': A -> A -> Prop} {lub} {CL: CompleteLattice_Setoid R R' lub} (f: A -> A): A :=
  glb_of_lub R lub (greater_than_fp f R).

Lemma lub_less_than {A: Type} {R R': A -> A -> Prop} {lub} {CL: CompleteLattice_Setoid R R' lub}: forall (X: A -> Prop) y,
  (forall x, X x -> R x y) ->
  R (lub X) y.
Proof.
  intros.
  pose proof CL_Complete_lub X as [? ?].
  apply H1.
  auto.
Qed.

Lemma less_than_lub {A: Type} {R R': A -> A -> Prop} {lub} {CL: CompleteLattice_Setoid R R' lub}: forall x y (Y: A -> Prop),
  Y y ->
  R x y ->
  R x (lub Y).
Proof.
  intros.
  pose proof CL_Complete_lub Y as [? ?].
  rewrite H0.
  apply H1.
  auto.
Qed.

Lemma element_less_than_lub {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall x (X: A -> Prop),
  X x ->
  R x (lub X).
Proof.
  intros.
  apply less_than_lub with x; [| reflexivity].
  auto.
Qed.

Lemma CL_Complete_glb {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall T, greatest_lower_bound R T (glb_of_lub R lub T).
Proof.
  intros.
  hnf; intros.
  split.
  + hnf; intros.
    unfold glb_of_lub.
    apply lub_less_than.
    intros.
    auto.
  + intros.
    unfold glb_of_lub.
    apply element_less_than_lub; auto.
Qed.

Lemma glb_congr {A: Type} {R R': A -> A -> Prop} {lub} {CL: CompleteLattice_Setoid R R' lub}: forall T1 T2, (forall a, T1 a <-> T2 a) -> R' (glb_of_lub R lub T1) (glb_of_lub R lub T2).
Proof.
  intros.
  unfold glb_of_lub.
  apply lub_congr.
  intros.
  unfold lower_bound.
  apply all_iff_morphism; intros ?.
  rewrite H; tauto.
Qed.

Lemma less_than_glb {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall (X: A -> Prop) y,
  (forall x, X x -> R y x) ->
  R y (glb_of_lub R lub X).
Proof.
  intros.
  pose proof CL_Complete_glb X as [? ?].
  apply H1.
  auto.
Qed.

Lemma glb_less_than {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall x y (Y: A -> Prop),
  Y y ->
  R y x ->
  R (glb_of_lub R lub Y) x.
Proof.
  intros.
  pose proof CL_Complete_glb Y as [? ?].
  rewrite <- H0.
  apply H1.
  auto.
Qed.

Lemma glb_less_than_element {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall x (X: A -> Prop),
  X x ->
  R (glb_of_lub R lub X) x.
Proof.
  intros.
  apply glb_less_than with x; [| reflexivity].
  auto.
Qed.

Lemma KnasterTarski_fixpoint_theorem_g {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall f,
  Proper (R ==> R) f ->
  R' (KT_fix_g f) (f (KT_fix_g f)).
Proof.
  intros.
  assert (R (KT_fix_g f) (f (KT_fix_g f))).
  {
    unfold KT_fix_g.
    apply lub_less_than.
    intros.
    hnf in H0.
    rewrite H0.
    apply H.
    apply element_less_than_lub; auto.
  }
  apply antisymmetricity_setoid; auto.
  pose proof H _ _ H0: lower_than_fp f R ((f (KT_fix_g f))).
  apply element_less_than_lub in H1.
  auto.
Qed.
  
Lemma KnasterTarski_fixpoint_greatest_fixpoint {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall f x,
  Proper (R ==> R) f ->
  R' x (f x) ->
  R x (KT_fix_g f).
Proof.
  intros.
  pose proof CL_Complete_lub (lower_than_fp f R) as [? ?].
  apply H1.
  hnf.
  rewrite <- H0.
  reflexivity.
Qed.

Lemma KnasterTarski_fixpoint_theorem_l {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall f,
  Proper (R ==> R) f ->
  R' (KT_fix_l f) (f (KT_fix_l f)).
Proof.
  intros.
  assert (R (f (KT_fix_l f)) (KT_fix_l f)).
  {
    unfold KT_fix_l.
    apply less_than_glb.
    intros.
    hnf in H0.
    rewrite <- H0.
    apply H.
    apply glb_less_than_element; auto.
  }
  apply antisymmetricity_setoid; auto.
  pose proof H _ _ H0: greater_than_fp f R ((f (KT_fix_l f))).
  apply glb_less_than_element in H1.
  auto.
Qed.
  
Lemma KnasterTarski_fixpoint_least_fixpoint {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall f x,
  Proper (R ==> R) f ->
  R' x (f x) ->
  R (KT_fix_l f) x.
Proof.
  intros.
  pose proof CL_Complete_glb (greater_than_fp f R) as [? ?].
  apply H1.
  hnf.
  rewrite <- H0.
  reflexivity.
Qed.

Lemma KnasterTarski_fixpoint_least_prefixpoint {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}: forall f x,
  Proper (R ==> R) f ->
  R (f x) x ->
  R (KT_fix_l f) x.
Proof.
  intros.
  pose proof CL_Complete_glb (greater_than_fp f R) as [? ?].
  apply H1.
  hnf.
  auto.
Qed.

Lemma least_fixpoint_mono {A: Type} {R R': A -> A -> Prop} {lub} {Equ: Equivalence R'} {CL: CompleteLattice_Setoid R R' lub}:
  forall f g,
    Proper (R ==> R) f ->
    Proper (R ==> R) g ->
    lift_rel2 R f g ->
    R (KT_fix_l f) (KT_fix_l g).
Proof.
  intros.
  apply KnasterTarski_fixpoint_least_prefixpoint; auto.
  rewrite (KnasterTarski_fixpoint_theorem_l g) at 2 by auto.
  apply H1.
Qed.

Class CL_Domain (A:Type): Type :=
{
  Domain_R: A -> A -> Prop;
  Domain_R': A -> A -> Prop;
  Domain_lub: (A -> Prop) -> A;
  Domain_Equiv: Equivalence Domain_R';
  Domain_CompleteLattice: CompleteLattice_Setoid Domain_R Domain_R' Domain_lub;
}.

Existing Instances Domain_Equiv Domain_CompleteLattice.

Lemma lift_complete_lattice {X A R R' lub} (CL: @CompleteLattice_Setoid A R R' lub):
  @CompleteLattice_Setoid (X -> A) (lift_rel2 R) (lift_rel2 R') (lift_set_summary lub).
Proof.
  constructor.
  + constructor; hnf; intros.
    - intros ?; apply antisymmetricity_setoid; auto.
    - intros ?; apply PO_Reflexive_Setoid; auto.
    - intros ?; eapply transitivity; eauto.
  + intros.
    split.
    - hnf; intros.
      intros ?.
      refine (proj1 (CL_Complete_lub _) _ _).
      eauto.
    - intros.
      intros ?.
      refine (proj2 (CL_Complete_lub _) _ _).
      hnf; intros.
      destruct H0 as [? [? ?]]; subst.
      apply (H x); auto.
  + intros.
    intros ?.
    unfold lift_set_summary.
    apply lub_congr.
    intros. apply ex_iff_morphism.
    intros ?.
    specialize (H a1); tauto.
Qed.

Instance Lift_CL_Domain (A B: Type) {CL: CL_Domain B}: CL_Domain (A -> B) :=
    Build_CL_Domain (A -> B) (lift_rel2 Domain_R) (lift_rel2 Domain_R') (lift_set_summary Domain_lub) ltac:(apply pointwise_equivalence; typeclasses eauto) (lift_complete_lattice Domain_CompleteLattice).

Lemma pair_CL
        {A B AB: Type}
        (projA: AB -> A)
        (projB: AB -> B)
        {RA RA': A -> A -> Prop}
        {RB RB': B -> B -> Prop}
        (RAB RAB': AB -> AB -> Prop)
        {lubA lubB} lubAB
        (CLA: CompleteLattice_Setoid RA RA' lubA)
        (CLB: CompleteLattice_Setoid RB RB' lubB):
  (forall c1 c2, RAB c1 c2 <-> RA (projA c1) (projA c2) /\ RB (projB c1) (projB c2)) ->
  (forall c1 c2, RAB' c1 c2 <-> RA' (projA c1) (projA c2) /\ RB' (projB c1) (projB c2)) ->
  (forall cs, projA (lubAB cs) = lubA (fun a => exists c, cs c /\ projA c = a) /\
              projB (lubAB cs) = lubB (fun b => exists c, cs c /\ projB c = b)) ->
  (forall c1 c2, projA c1 = projA c2 -> projB c1 = projB c2 -> c1 = c2) ->
  @CompleteLattice_Setoid AB RAB RAB' lubAB.
Proof.
  intros HR HR' Hlub Hproj.
  constructor.
  + constructor.
    - hnf; intros.
      rewrite HR in H, H0; rewrite HR'.
      destruct H, H0.
      split; apply antisymmetricity_setoid; auto.
    - intros.
      rewrite HR' in H; rewrite HR.
      destruct H.
      split; apply PO_Reflexive_Setoid; auto.
    - hnf; intros.
      rewrite HR in H, H0 |- *.
      destruct H, H0.
      split; etransitivity; eauto.
  + intros.
    hnf; intros.
    split.
    - hnf; intros.
      rewrite HR.
      rewrite (proj1 (Hlub _)), (proj2 (Hlub _)).
      split; apply (proj1 (CL_Complete_lub _)); eauto.
    - intros.
      rewrite HR.
      rewrite (proj1 (Hlub _)), (proj2 (Hlub _)).
      split; apply (proj2 (CL_Complete_lub _)).
      * hnf.
        intros a [c [? ?]]; subst.
        specialize (H _ H0).
        rewrite HR in H; tauto.
      * hnf.
        intros a [c [? ?]]; subst.
        specialize (H _ H0).
        rewrite HR in H; tauto.
  + intros.       
    rewrite HR'.
    rewrite !(proj1 (Hlub _)), !(proj2 (Hlub _)). 
    split; apply lub_congr; intros; apply ex_iff_morphism; intros ?.
    - rewrite H; tauto.
    - rewrite H; tauto.
Qed.    

Lemma prod_pair_CL
        {A B: Type}
        {RA RA': A -> A -> Prop}
        {RB RB': B -> B -> Prop}
        {lubA lubB}
        {CLA: CompleteLattice_Setoid RA RA' lubA}
        {CLB: CompleteLattice_Setoid RB RB' lubB}:
  @CompleteLattice_Setoid
    (A * B)
    (pair_rel2 RA RB)
    (pair_rel2 RA' RB')
    (pair_set_summary lubA lubB).
Proof.
  apply (pair_CL fst snd _ _ _ CLA CLB).
  + intros; reflexivity.
  + intros; reflexivity.
  + intros; split; reflexivity.
  + intros [? ?] [? ?]; simpl; intros; subst; reflexivity.
Qed.

Instance Pair_CL_Domain (A B: Type) {CLA: CL_Domain A} {CLB: CL_Domain B}: CL_Domain (A * B) :=
  Build_CL_Domain
    (A * B)
    (pair_rel2 Domain_R Domain_R)
    (pair_rel2 Domain_R' Domain_R')
    (pair_set_summary Domain_lub Domain_lub)
    ltac:(refine (RelProd_Equivalence _ _ _ _); typeclasses eauto)
    (prod_pair_CL).

Definition KT_fix2_l
             {A B}
             {RA RA': A -> A -> Prop}
             {RB RB': B -> B -> Prop}
             {lubA lubB}
             {CLA: CompleteLattice_Setoid RA RA' lubA}
             {CLB: CompleteLattice_Setoid RB RB' lubB}
             (f: A -> B -> A) (g: A -> B -> B): A * B :=
  @KT_fix_l
    (A * B) _ _ _ prod_pair_CL
    (fun c => (f (fst c) (snd c), g (fst c) (snd c))).

Corollary two_dimensional_fix_coincide:
  forall {A B: Type}
         {RA RA': A -> A -> Prop}
         {RB RB': B -> B -> Prop}
         {lubA lubB}
         {equA: Equivalence RA'}
         {equB: Equivalence RB'}
         {CLA: CompleteLattice_Setoid RA RA' lubA}
         {CLB: CompleteLattice_Setoid RB RB' lubB},
  forall (f: A -> B -> A) (g: A -> B -> B)
    (Hf_ProperR: Proper (RA ==> RB ==> RA) f)
    (Hg_ProperR: Proper (RA ==> RB ==> RB) g),
    (pair_rel2 RA' RB')
      (KT_fix2_l f g)
      (KT_fix2_l (fun _ b => KT_fix_l (fun a => f a b)) (fun a _ => KT_fix_l (fun b => g a b))).
Proof.
  intros.
  assert (Proper (RA' ==> RB' ==> RA') f) as Hf_ProperR'.
  {
    hnf; intros; hnf; intros.
    apply antisymmetricity_setoid.
    + apply Hf_ProperR; [rewrite H | rewrite H0]; reflexivity.
    + apply Hf_ProperR; [rewrite H | rewrite H0]; reflexivity.
  }
  assert (Proper (RA' ==> RB' ==> RB') g) as Hg_ProperR'.
  {
    hnf; intros; hnf; intros.
    apply antisymmetricity_setoid.
    + apply Hg_ProperR; [rewrite H | rewrite H0]; reflexivity.
    + apply Hg_ProperR; [rewrite H | rewrite H0]; reflexivity.
  }
  assert (forall b, Proper (RA ==> RA) (fun a => f a b)) as Hf_mono.
  {
    intros; hnf; intros.
    apply Hf_ProperR; auto.
    reflexivity.
  }
  assert (forall a, Proper (RB ==> RB) (fun b => g a b)) as Hg_mono.
  {
    intros; hnf; intros.
    apply Hg_ProperR; auto.
    reflexivity.
  }
  assert (Equivalence (pair_rel2 RA' RB')) as equAB by (apply RelProd_Equivalence; auto).
  set (h := fun c => (f (fst c) (snd c), g (fst c) (snd c))).
  set (h' := fun c => (KT_fix_l (fun a => f a (snd c)), KT_fix_l (fun b => g (fst c) b))).
  assert (Proper (pair_rel2 RA RB ==> pair_rel2 RA RB) h) as Hh_ProperR.
  {
    hnf; intros [? ?] [? ?] [? ?].
    split; [apply Hf_ProperR | apply Hg_ProperR]; auto.
  }
  assert (Proper (pair_rel2 RA RB ==> pair_rel2 RA RB) h') as Hh'_ProperR.
  {
    hnf; intros [? ?] [? ?] [? ?].
    split; simpl.
    + apply least_fixpoint_mono; auto.
      hnf; intros; simpl in H0 |- *.
      rewrite H0; reflexivity.
    + apply least_fixpoint_mono; auto.
      hnf; intros; simpl in H |- *.
      rewrite H; reflexivity.
  }
  assert (pair_rel2 RA' RB'
            (@KT_fix_l _ _ _ _ (prod_pair_CL) h')
            (h (@KT_fix_l _ _ _ _ (prod_pair_CL) h'))) as Hfix1.
  {
    pose proof (@KnasterTarski_fixpoint_theorem_l _ _ _ _ _ (prod_pair_CL) h') _ as [? ?].
    split.
    + unfold h' at 2 in H.
      unfold fst at 2 in H.
      pose proof (@KnasterTarski_fixpoint_theorem_l _ _ _ _ _ CLA (fun a => f a (snd (@KT_fix_l _ _ _ _ (prod_pair_CL) h'))) _).
      cbv beta in H1.
      rewrite <- H in H1.
      exact H1.
    + unfold h' at 2 in H0.
      unfold snd at 2 in H0.
      pose proof (@KnasterTarski_fixpoint_theorem_l _ _ _ _ _ CLB (fun b => g (fst (@KT_fix_l _ _ _ _ (prod_pair_CL) h')) b) _).
      cbv beta in H1.
      rewrite <- H0 in H1.
      exact H1.
  }
  apply (@KnasterTarski_fixpoint_least_fixpoint _ _ _ _ _ (prod_pair_CL)) in Hfix1; auto.
  assert (pair_rel2 RA RB
            (h' (@KT_fix_l _ _ _ _ (prod_pair_CL) h))
            (@KT_fix_l _ _ _ _ (prod_pair_CL) h)) as Hfix2.
  {
    pose proof (@KnasterTarski_fixpoint_theorem_l _ _ _ _ _ (prod_pair_CL) h) _ as [? ?].
    split.
    + unfold h'.
      unfold fst at 1.
      apply KnasterTarski_fixpoint_least_fixpoint; auto.
    + unfold h'.
      unfold snd at 1.
      apply KnasterTarski_fixpoint_least_fixpoint; auto.
  }
  apply (@KnasterTarski_fixpoint_least_prefixpoint _ _ _ _ _ (prod_pair_CL)) in Hfix2; auto.
  pose proof (@prod_pair_CL A B _ _ _ _ _ _ _ _).
  apply antisymmetricity_setoid; auto.
Qed.
