Require Import VCF.GeneralDomain.
Require Import VCF.KnasterTarski.
Require Import VCF.ZFuncDomain.
Require Import Equivalence.
Require Import Morphisms.
Require Import Morphisms_Prop.
Require Import Classical.
Require Import Psatz.
Require Import Basics.

Module Sets.

Class SETS (T: Type): Type :=
{
  full: T;
  empty: T;
  intersect: T -> T -> T;
  union: T -> T -> T;
  omega_intersect: (T -> Prop) -> T;
  omega_union: (T -> Prop) -> T;
  equiv: T -> T -> Prop;
  included: T -> T -> Prop;
}.

Definition complement {A: Type} (X: A -> Prop) := fun a => ~ X a.

Definition lift_full {A B} {_SETS: SETS B}: A -> B := fun _ => full.

Definition lift_empty {A B} {_SETS: SETS B}: A -> B := fun _ => empty.

Definition lift_intersect {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> (A -> B) :=
  fun x y a => intersect (x a) (y a).

Definition lift_union {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> (A -> B) :=
  fun x y a => union (x a) (y a).

Definition lift_omega_intersect {A B} {_SETS: SETS B}: ((A -> B) -> Prop) -> (A -> B) :=
  fun x a => omega_intersect (fun b => exists f, x f /\ f a = b).

Definition lift_omega_union {A B} {_SETS: SETS B}: ((A -> B) -> Prop) -> (A -> B) :=
  fun x a => omega_union (fun b => exists f, x f /\ f a = b).

Definition lift_equiv {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> Prop :=
  fun x y => forall a, equiv (x a) (y a).

Definition lift_included {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> Prop :=
  fun x y => forall a, included (x a) (y a).

End Sets.

Instance Prop_SETS: Sets.SETS Prop :=
  {|
    Sets.full := True;
    Sets.empty := False;
    Sets.intersect := and;
    Sets.union := or;
    Sets.omega_intersect := fun S => forall P, S P -> P;
    Sets.omega_union := fun S => exists P, S P /\ P;
    Sets.equiv := iff;
    Sets.included := fun P Q => P -> Q
  |}.

Instance lift_SETS (A B: Type) (_SETS: Sets.SETS B): Sets.SETS (A -> B) :=
  {|
    Sets.full := Sets.lift_full;
    Sets.empty := Sets.lift_empty;
    Sets.intersect := Sets.lift_intersect;
    Sets.union := Sets.lift_union;
    Sets.omega_intersect := Sets.lift_omega_intersect;
    Sets.omega_union := Sets.lift_omega_union;
    Sets.equiv := Sets.lift_equiv;
    Sets.included := Sets.lift_included
  |}.

Ltac no_extra_simplify T :=
  idtac.

Ltac SETS_simplify T tac :=
  first
    [ match T with
      | _ _ (lift_SETS _ _ _) => idtac
      end;
      let T1 := eval simpl in T in
      let T2 := eval cbv delta
            [Sets.lift_full
             Sets.lift_empty
             Sets.lift_intersect
             Sets.lift_union
             Sets.lift_omega_intersect
             Sets.lift_omega_union
             Sets.lift_equiv
             Sets.lift_included] in T1 in
      change T with T2;
      SETS_simplify T2 tac
    | match T with
      | _ _ Prop_SETS => idtac
      end;
      let T1 := eval simpl in T in
      change T with T1
    | tac T
    ].

Ltac unfold_SETS_tac tac :=
  repeat
  match goal with
  | |- context [@Sets.full ?T ?_SETS] =>
         SETS_simplify (@Sets.full T _SETS) tac
  | |- context [@Sets.empty ?T ?_SETS] =>
         SETS_simplify (@Sets.empty T _SETS) tac
  | |- context [@Sets.equiv ?T ?_SETS] =>
         SETS_simplify (@Sets.equiv T _SETS) tac
  | |- context [@Sets.intersect ?T ?_SETS] =>
         SETS_simplify (@Sets.intersect T _SETS) tac
  | |- context [@Sets.union ?T ?_SETS] =>
         SETS_simplify (@Sets.union T _SETS) tac
  | |- context [@Sets.omega_intersect ?T ?_SETS] =>
         SETS_simplify (@Sets.omega_intersect T _SETS) tac
  | |- context [@Sets.omega_union ?T ?_SETS] =>
         SETS_simplify (@Sets.omega_union T _SETS) tac
  | |- context [@Sets.included ?T ?_SETS] =>
         SETS_simplify (@Sets.included T _SETS) tac
  | |- _ => progress cbv beta
  end.
  
Class SETS_Properties (T: Type) {_SETS: Sets.SETS T}: Prop :=
{
  Sets_included_refl: Reflexive Sets.included;
  Sets_included_trans: Transitive Sets.included;
  Sets_equiv_Sets_included: forall x y, Sets.equiv x y <-> (Sets.included x y /\ Sets.included y x);
  Sets_empty_included: forall x, Sets.included Sets.empty x;
  Sets_included_full: forall x, Sets.included x Sets.full;
  Sets_intersect_included1: forall x y, Sets.included (Sets.intersect x y) x;
  Sets_intersect_included2: forall x y, Sets.included (Sets.intersect x y) y;
  Sets_included_intersect: forall x y z, Sets.included x y -> Sets.included x z -> Sets.included x (Sets.intersect y z);
  Sets_included_union1: forall x y, Sets.included x (Sets.union x y);
  Sets_included_union2: forall x y, Sets.included y (Sets.union x y);
  Sets_union_included_strong2: forall x y z u, Sets.included (Sets.intersect x u) z -> Sets.included (Sets.intersect y u) z -> Sets.included (Sets.intersect (Sets.union x y) u) z;
  Sets_included_omega_union: forall (xs: _ -> Prop) x, xs x -> Sets.included x (Sets.omega_union xs);
  Sets_omega_union_included: forall (xs: _ -> Prop) y, (forall x, xs x -> Sets.included x y) -> Sets.included (Sets.omega_union xs) y;
  Sets_omega_intersect_included: forall (xs: _ -> Prop) x, xs x -> Sets.included (Sets.omega_intersect xs) x;
  Sets_included_omega_intersect: forall (xs: _ -> Prop) y, (forall x, xs x -> Sets.included y x) -> Sets.included y (Sets.omega_intersect xs);
}.

Existing Instances Sets_included_refl
                   Sets_included_trans.

Instance Sets_equiv_refl {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Reflexive Sets.equiv.
Proof.
  hnf; intros.
  apply Sets_equiv_Sets_included.
  split; apply Sets_included_refl.
Qed.

Instance Sets_equiv_sym {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Symmetric Sets.equiv.
Proof.
  hnf; intros.
  rewrite Sets_equiv_Sets_included in H |- *.
  tauto.
Qed.

Instance Sets_equiv_trans {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Transitive Sets.equiv.
Proof.
  hnf; intros.
  rewrite Sets_equiv_Sets_included in H, H0 |- *.
  destruct H, H0.
  split; eapply Sets_included_trans; eauto.
Qed.

Instance Sets_equiv_equiv {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Equivalence Sets.equiv.
Proof.
  constructor; auto.
  + apply Sets_equiv_refl; auto.
  + apply Sets_equiv_sym; auto.
  + apply Sets_equiv_trans; auto.
Qed.

Instance Sets_included_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> iff) Sets.included.
Proof.
  unfold Proper, respectful.
  intros.
  rewrite Sets_equiv_Sets_included in H, H0.
  destruct H, H0.
  split; intros;
  repeat (eapply Sets_included_trans; eauto).
Qed.

Lemma Sets_intersect_full {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.equiv (Sets.intersect x Sets.full) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_intersect_included1.
  + apply Sets_included_intersect.
    - reflexivity.
    - apply Sets_included_full.
Qed.

Lemma Sets_union_included {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z, Sets.included x z -> Sets.included y z -> Sets.included (Sets.union x y) z.
Proof.
  intros.
  pose proof Sets_union_included_strong2 x y z Sets.full.
  rewrite !Sets_intersect_full in H1.
  auto.
Qed.

Instance Sets_union_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included ==> Sets.included) Sets.union.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_union_included.
  + apply Sets_included_trans with y; auto.
    apply Sets_included_union1.
  + apply Sets_included_trans with y0; auto.
    apply Sets_included_union2.
Qed.

Instance Sets_union_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) Sets.union.
Proof.
  hnf; intros; hnf; intros.
  apply Sets_equiv_Sets_included in H.
  apply Sets_equiv_Sets_included in H0.
  apply Sets_equiv_Sets_included; split;
  apply Sets_union_mono; tauto.
Qed.

Instance Sets_intersect_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included ==> Sets.included) Sets.intersect.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_included_intersect.
  + rewrite <- H.
    apply Sets_intersect_included1.
  + rewrite <- H0.
    apply Sets_intersect_included2.
Qed.

Instance Sets_intersect_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) Sets.intersect.
Proof.
  hnf; intros; hnf; intros.
  apply Sets_equiv_Sets_included in H.
  apply Sets_equiv_Sets_included in H0.
  apply Sets_equiv_Sets_included; split;
  apply Sets_intersect_mono; tauto.
Qed.

Lemma Sets_intersect_absorb1 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.equiv (Sets.intersect x y) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_intersect_included1.
  + apply Sets_included_intersect.
    - reflexivity.
    - auto.
Qed.

Lemma Sets_intersect_absorb2 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.equiv (Sets.intersect y x) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_intersect_included2.
  + apply Sets_included_intersect.
    - auto.
    - reflexivity.
Qed.

Lemma union_comm {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x y,
  Sets.equiv (Sets.union x y) (Sets.union y x).
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split; apply Sets_union_included;
  first [ apply Sets_included_union1 | apply Sets_included_union2 ].
Qed.

Lemma Sets_intersect_comm {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x y,
  Sets.equiv (Sets.intersect x y) (Sets.intersect y x).
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split; apply Sets_included_intersect;
  first [ apply Sets_intersect_included1 | apply Sets_intersect_included2 ].
Qed.

Lemma Sets_union_included_strong1 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z u, Sets.included (Sets.intersect u x) z -> Sets.included (Sets.intersect u y) z -> Sets.included (Sets.intersect u (Sets.union x y)) z.
Proof.
  intros.
  rewrite Sets_intersect_comm in H, H0 |- *.
  apply Sets_union_included_strong2; auto.
Qed.

Lemma union_empty {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.union x Sets.empty) x.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - reflexivity.
    - apply Sets_empty_included.
  + apply Sets_included_union1.
Qed.

Lemma empty_union {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.union Sets.empty x) x.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - apply Sets_empty_included.
    - reflexivity.
  + apply Sets_included_union2.
Qed.

Instance Prop_SETS_Properties: SETS_Properties Prop.
Proof.
  constructor; unfold Proper, respectful; unfold_SETS_tac idtac; simpl;
  hnf; intros; try tauto.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
Qed.

Instance lift_SETS_Properties (A B: Type) (_SETS: Sets.SETS B) (_SETS_Properties: SETS_Properties B): SETS_Properties (A -> B).
Proof.
  constructor; unfold Proper, respectful; unfold_SETS_tac no_extra_simplify; hnf; intros.
  + apply Sets_included_refl.
  + eapply Sets_included_trans; eauto.
  + split; intros.
    - split; intros; specialize (H a);
      rewrite Sets_equiv_Sets_included in H;
      tauto.
    - destruct H.
      intros.
      rewrite Sets_equiv_Sets_included; auto.
  + apply Sets_empty_included.
  + apply Sets_included_full.
  + apply Sets_intersect_included1.
  + apply Sets_intersect_included2.
  + apply Sets_included_intersect; auto.
  + apply Sets_included_union1.
  + apply Sets_included_union2.
  + apply Sets_union_included_strong2; auto.
  + apply Sets_included_omega_union.
    exists x; auto.
  + apply Sets_omega_union_included.
    intros ? [? [? ?]].
    subst.
    auto.
  + apply Sets_omega_intersect_included.
    exists x; auto.
  + apply Sets_included_omega_intersect.
    intros ? [? [? ?]].
    subst.
    auto.
Qed.

Instance Sets_complement_equiv A:
  Proper (Sets.equiv ==> Sets.equiv) (@Sets.complement A).
Proof.
  unfold Proper, respectful; unfold_SETS_tac idtac.
  unfold Sets.complement.
  intros S1 S2 ?.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_complement_complement: forall A (S: A -> Prop),
  Sets.equiv (Sets.complement (Sets.complement S)) S.
Proof.
  intros.
  unfold Sets.complement; unfold_SETS_tac idtac.
  intros.
  tauto.
Qed.

Instance Func_test_eq_equiv A:
  Proper (@ZFunc.equiv A ==> @ZFunc.equiv A ==> Sets.equiv) ZFunc.test_eq.
Proof.
  unfold Proper, respectful.
  unfold ZFunc.equiv, ZFunc.test_eq.
  unfold_SETS_tac idtac.
  intros f1 f2 ? g1 g2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Instance Func_test_le_equiv A:
  Proper (@ZFunc.equiv A ==> @ZFunc.equiv A ==> Sets.equiv) ZFunc.test_le.
Proof.
  unfold Proper, respectful.
  unfold ZFunc.equiv, ZFunc.test_le.
  unfold_SETS_tac idtac.
  intros f1 f2 ? g1 g2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Ltac solve_mono tac :=
  match goal with
  | |- Sets.included ?A ?A =>
         reflexivity
  | |- Sets.included (Sets.union _ _) (Sets.union _ _) =>
         refine (Sets_union_mono _ _ _ _ _ _); solve_mono tac
  | |- _ => first [assumption | tac]
  end.

Lemma SETS_included_CL {A: Type} {_SETS: Sets.SETS A} {_SETS_Properties: SETS_Properties A}:
  CompleteLattice_Setoid Sets.included Sets.equiv Sets.omega_union.
Proof.
  constructor.
  + constructor; hnf; intros.
    - apply Sets_equiv_Sets_included; auto.
    - rewrite H; reflexivity.
    - rewrite H; auto.
  + intros; hnf; intros.
    split; intros.
    - hnf; intros.
      apply Sets_included_omega_union; intros.
      auto.
    - apply Sets_omega_union_included.
      auto.
  + intros.
    apply Sets_equiv_Sets_included; auto.
    split; apply Sets_omega_union_included; intros;
    apply Sets_included_omega_union; apply H; auto.
Qed.

Lemma SETS_flip_included_CL {A: Type} {_SETS: Sets.SETS A} {_SETS_Properties: SETS_Properties A}:
  CompleteLattice_Setoid (flip Sets.included) Sets.equiv Sets.omega_intersect.
Proof.
  constructor.
  + constructor; hnf; intros.
    - apply Sets_equiv_Sets_included; auto.
    - rewrite H; reflexivity.
    - rewrite H; auto.
  + intros; hnf; intros.
    split; intros.
    - hnf; intros.
      apply Sets_omega_intersect_included; intros.
      auto.
    - apply Sets_included_omega_intersect.
      auto.
  + intros.
    apply Sets_equiv_Sets_included; auto.
    split; apply Sets_included_omega_intersect; intros;
    apply Sets_omega_intersect_included; apply H; auto.
Qed.

Definition SETS_included_CL_Domain {A: Type} {_SETS: Sets.SETS A} {_SETS_Properties: SETS_Properties A}: CL_Domain A :=
  Build_CL_Domain
    A
    Sets.included
    Sets.equiv
    Sets.omega_union
    ltac:(typeclasses eauto)
    SETS_included_CL.

Definition SETS_flip_included_CL_Domain {A: Type} {_SETS: Sets.SETS A} {_SETS_Properties: SETS_Properties A}: CL_Domain A :=
  Build_CL_Domain
    A
    (flip Sets.included)
    Sets.equiv
    Sets.omega_intersect
    ltac:(typeclasses eauto)
    (SETS_flip_included_CL).

Lemma SETS_included_Union_Domain {A: Type} {_SETS: Sets.SETS A} {_SETS_Properties: SETS_Properties A}: @Union_Domain A (SETS_included_CL_Domain).
Proof.
  apply (Build_Union_Domain
           A
           _
           Sets.union
           Sets.empty).
  typeclasses eauto.
Defined.

Lemma SETS_flip_included_Union_Domain {A: Type} {_SETS: Sets.SETS A} {_SETS_Properties: SETS_Properties A}: @Union_Domain A (SETS_flip_included_CL_Domain).
Proof.
  apply (Build_Union_Domain
           A
           _
           Sets.union
           Sets.empty).
  simpl.
  hnf; intros; hnf; intros.
  unfold flip in *.
  rewrite H, H0.
  reflexivity.
Defined.
