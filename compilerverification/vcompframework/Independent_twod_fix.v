Require Import ClassicalFacts.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationPairs.
Require Import VCF.BoubakiWitt.
Require Import VCF.KnasterTarski.

(** TODO:Independent **)
Record FixPointTheoremStatement: Type := {
  OrderAssumption: forall A (eqA R: A -> A -> Prop), Type;
  FunctionAssumption: forall A (eqA R: A -> A -> Prop), OrderAssumption A eqA R -> (A -> A) -> Prop;
  Fix: forall A (eqA R: A -> A -> Prop)(OA: OrderAssumption A eqA R),
      (A -> A) -> A;
  FPSound: forall A (eqA R: A -> A -> Prop) (OA: OrderAssumption A eqA R) (F: A -> A),
    FunctionAssumption A eqA R OA F ->
    eqA (F (Fix A eqA R OA F)) (Fix A eqA R OA F);
  FPLeast: forall A (eqA R: A -> A -> Prop) (OA: OrderAssumption A eqA R) (F: A -> A),
    FunctionAssumption A eqA R OA F ->
    forall x, eqA (F x) x -> R (Fix A eqA R OA F) x
}.

Section Two_d_fixpoint.

Context      {stmt1: FixPointTheoremStatement}
             {stmt2: FixPointTheoremStatement}.
             
Class Two_d_orderassumption (AB: Type) (eqAB RAB: AB -> AB -> Prop):Type:={
  A:Type;
  B:Type;
  RA: A -> A -> Prop;
  RA': AB -> AB -> Prop;
  eqA: A -> A -> Prop;
  eqA': AB -> AB -> Prop;
  RB: B -> B -> Prop;
  RB': AB -> AB -> Prop;
  eqB: B -> B -> Prop;
  eqB': AB -> AB -> Prop;
  projA: AB -> A;
  projB: AB -> B;
  BuildAB: A -> B -> AB;
  CombineAB: forall c, BuildAB (projA c) (projB c) = c;
  SplitA: forall a b, projA (BuildAB a b) = a;
  SplitB: forall a b, projB (BuildAB a b) = b;
  EA: Equivalence eqA;
  EB: Equivalence eqB;
  OA': OrderAssumption stmt1 AB eqA' RA';
  OB': OrderAssumption stmt2 AB eqB' RB';
  L1: forall c1 c2, RAB c1 c2 <-> (RA (projA c1) (projA c2) /\ ~ RA (projA c2) (projA c1))\/ (RA (projA c1) (projA c2) /\ RA (projA c2) (projA c1) /\ RB (projB c1)  (projB c2));
  L2: forall c1 c2, eqAB c1 c2 <-> eqA (projA c1) (projA c2) /\ eqB (projB c1) (projB c2);
  L_RA: forall c1 c2, RA' c1 c2 <-> RA (projA c1) (projA c2);
  L_eqA: forall c1 c2, eqA' c1 c2 <-> eqA (projA c1) (projA c2);
  L_RB: forall c1 c2, RB' c1 c2 <-> RB (projB c1) (projB c2);
  L_eqB: forall c1 c2, eqB' c1 c2 <-> eqB (projB c1) (projB c2);
}.

Definition Two_d_functionassumption (AB: Type) (eqAB RAB: AB -> AB -> Prop) (OAB:Two_d_orderassumption AB eqAB RAB)(h: AB -> AB):Prop:=
  (forall a b, eqA (projA a) (projA b) <-> eqA (projA (h a)) (projA (h b)))/\
  (forall a b, eqA (projA a) (projA b)/\ eqB (projB a) (projB b) <-> eqB (projB (h a)) (projB (h b)))
  /\ Proper (eqAB ==> eqAB) h
  /\ FunctionAssumption stmt1 AB eqA' RA' OA' h
  /\ (forall a, FunctionAssumption stmt2 AB eqB' RB' OB' (fun c => BuildAB a (projB (h c))))
  /\ (forall a, eqA a (projA (Fix stmt2 AB eqB' RB' OB' (fun c => BuildAB a (projB (h c)))))).

Definition Two_d_fix (AB:Type) (eqAB RAB: AB -> AB -> Prop) (OAB:Two_d_orderassumption AB eqAB RAB) (h: AB -> AB):AB:=
(BuildAB (projA (Fix stmt1 AB eqA' RA' OA' h)) 
(projB (Fix stmt2 AB eqB' RB' OB' (fun c =>BuildAB (projA (Fix stmt1 AB eqA' RA' OA' h)) (projB (h c))) ))).

Theorem Two_d_FPSound (AB:Type) (eqAB RAB: AB -> AB -> Prop) (OAB:Two_d_orderassumption AB eqAB RAB) (h: AB -> AB) (F_ass: Two_d_functionassumption AB eqAB RAB OAB h):
eqAB (h (Two_d_fix AB eqAB RAB OAB h)) (Two_d_fix AB eqAB RAB OAB h ).
Proof.
  destruct F_ass as [H0 [H1 [H2 [H3 [H4 H5]]]]].
  apply L2;split.
  - unfold Two_d_fix. rewrite SplitA.
    pose proof (FPSound stmt1 AB eqA' RA' OA' h) H3.
    rewrite L_eqA in H.
    pose proof EA;destruct EA.
    eapply Equivalence_Transitive;[| apply H].
    rewrite <- H0. rewrite SplitA;auto.
  - unfold Two_d_fix. rewrite SplitB.
    specialize (H4 (projA (Fix stmt1 AB eqA' RA' OA' h))).
    pose proof (FPSound stmt2 AB eqB' RB' OB' (fun c : AB =>
                  BuildAB (projA (Fix stmt1 AB eqA' RA' OA' h)) (projB (h c)))) H4.
    clear H4.
    rewrite L_eqB in H.
    rewrite SplitB in H.
    pose proof EB;destruct EB.
    eapply Equivalence_Transitive;[|apply H].
    rewrite <- H1;split.
    * rewrite SplitA. auto.
    * rewrite SplitB. auto.
Qed.

Lemma RAB_to_A'_B' {AB:Type} {eqAB RAB: AB -> AB -> Prop} {OAB:Two_d_orderassumption AB eqAB RAB}:
  forall c1 c2, eqAB c1 c2 <-> (eqA' c1 c2 /\ eqB' c1 c2).
Proof.
  intros;rewrite L2,L_eqA,L_eqB;reflexivity.
Qed.
  
Theorem Two_d_FPLeast (AB:Type) (eqAB RAB: AB -> AB -> Prop) (OAB:Two_d_orderassumption AB eqAB RAB) (h: AB -> AB) (F_ass: Two_d_functionassumption AB eqAB RAB OAB h):
forall x, eqAB (h x) x -> RAB (Two_d_fix AB eqAB RAB OAB h) x.
Proof.
  intros;apply L1.
  pose proof classic (RA (projA x) (projA (Two_d_fix AB eqAB RAB OAB h))) as H0;destruct H0.
  - right;split.
    + unfold Two_d_fix. rewrite SplitA. 
      rewrite L2 in H. destruct H.
      rewrite <- (CombineAB x) in H.
      destruct F_ass as [? [? [? [? [? ?]]]]].
      rewrite SplitA in H.
      apply L_RA. apply FPLeast;auto.
      apply L_eqA. rewrite CombineAB in H;apply H.
    + split;eauto.
      rewrite L2 in H;destruct H.
      unfold Two_d_fix. rewrite SplitB.
      destruct F_ass as [? [? [? [? [? ?]]]]].
      pose proof FPLeast stmt2 AB eqB' RB' OB' (fun c : AB => BuildAB (projA (Fix stmt1 AB eqA' RA' OA' h)) (projB (h c))) (H6 (projA (Fix stmt1 AB eqA' RA' OA' h))) x.
      apply L_RB. apply H8;clear H8.
      apply L_eqB. rewrite SplitB;auto.
   - left;split. 
     rewrite L2 in H. destruct H.
     destruct F_ass as [? [? [? [? [? ?]]]]].
     unfold Two_d_fix. rewrite SplitA.
     apply L_RA.
     rewrite <- L_eqA in H.
     + apply (FPLeast stmt1 AB eqA' RA' OA' h H5 x H). 
     + auto.
Qed.

Definition Two_d_FixPointTheoremStatement:FixPointTheoremStatement:={|
  OrderAssumption:=Two_d_orderassumption;
  FunctionAssumption:=Two_d_functionassumption;
  Fix:=Two_d_fix;
  FPSound:=Two_d_FPSound;
  FPLeast:=Two_d_FPLeast;
|}.

End Two_d_fixpoint.