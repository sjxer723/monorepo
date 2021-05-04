Require Import ClassicalFacts.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import VCF.BoubakiWitt.
Require Import VCF.KnasterTarski.
Require Import VCF.InfSem.

Module L.

(** TODO:Dependent **)

Record FixPointTheoremStatement: Type := {
  OrderAssumption: forall A (eqA R: A -> A -> Prop), Type;
  FunctionAssumption: forall A (eqA R: A -> A -> Prop), OrderAssumption A eqA R -> (A -> A) -> Type;
  Fix: forall A (eqA R: A -> A -> Prop)(OA: OrderAssumption A eqA R) (F: A -> A) (F_ass: FunctionAssumption A eqA R OA F),
   A;
  FPSound: forall A (eqA R: A -> A -> Prop) (OA: OrderAssumption A eqA R) (F: A -> A)(F_ass: FunctionAssumption A eqA R OA F),
    eqA (F (Fix A eqA R OA F F_ass)) (Fix A eqA R OA F F_ass);
  FPLeast: forall A (eqA R: A -> A -> Prop) (OA: OrderAssumption A eqA R) (F: A -> A)(F_ass: FunctionAssumption A eqA R OA F),
    forall x, eqA (F x) x -> R (Fix A eqA R OA F F_ass) x
}.

Section Two_d_fixpoint.

Context      {stmt1: FixPointTheoremStatement}
             {stmt2: FixPointTheoremStatement}.
             
Class Two_d_orderassumption (AB: Type) (eqAB RAB: AB -> AB -> Prop):Type:={
  A:Type;
  B:Type;
  RA: A -> A -> Prop;
  eqA: A -> A -> Prop;
  RB: B -> B -> Prop;
  eqB: B -> B -> Prop;
  projA: AB -> A;
  projB: AB -> B;
  BuildAB: A -> B -> AB;
  CombineAB: forall c, BuildAB (projA c) (projB c) = c;
  SplitA: forall a b, projA (BuildAB a b) = a;
  SplitB: forall a b, projB (BuildAB a b) = b;
  POA: PartialOrder_Setoid RA eqA;
  POB: PartialOrder_Setoid RB eqB;
  EB: Equivalence eqB;
  OA: OrderAssumption stmt1 A eqA RA;
  OB: OrderAssumption stmt2 B eqB RB;
  L1: forall c1 c2, RAB c1 c2 <-> (RA (projA c1) (projA c2) /\ ~ RA (projA c2) (projA c1))\/ (RA (projA c1) (projA c2) /\ RA (projA c2) (projA c1) /\ RB (projB c1)  (projB c2));
  L2: forall c1 c2, eqAB c1 c2 <-> eqA (projA c1) (projA c2) /\ eqB (projB c1) (projB c2);
}.

Class Two_d_functionassumption (AB: Type) (eqAB RAB: AB -> AB -> Prop) (OAB:Two_d_orderassumption AB eqAB RAB)(h: AB -> AB):Type:={
  f: A -> A ;
  g: A -> B -> B;
  Split: forall c, h c = BuildAB (f (projA c)) (g (projA c) (projB c));
  Proper_f: Proper (eqA ==> eqA) f; 
  Proper_g: Proper (eqA ==> eqB ==> eqB) g;
  f_ass: FunctionAssumption stmt1 A eqA RA OA f;
  g_ass: forall a, FunctionAssumption stmt2 B eqB RB OB (g a);
}.

Definition Two_d_fix (AB:Type) (eqAB RAB: AB -> AB -> Prop) (OAB:Two_d_orderassumption AB eqAB RAB) (h: AB -> AB) (F_ass: Two_d_functionassumption AB eqAB RAB OAB h):=BuildAB (Fix stmt1 A eqA RA OA f f_ass)
(Fix stmt2 B eqB RB OB (g (Fix stmt1 A eqA RA OA f f_ass)) (g_ass (Fix stmt1 A eqA RA OA f f_ass))).

Theorem Two_d_FPSound (AB:Type) (eqAB RAB: AB -> AB -> Prop) (OAB:Two_d_orderassumption AB eqAB RAB) (h: AB -> AB) (F_ass: Two_d_functionassumption AB eqAB RAB OAB h):
eqAB (h (Two_d_fix AB eqAB RAB OAB h F_ass)) (Two_d_fix AB eqAB RAB OAB h F_ass).
Proof.
  apply L2;split.
  - rewrite Split, SplitA.
    unfold Two_d_fix;rewrite SplitA.
    apply (FPSound stmt1 A eqA RA OA f f_ass).
  - rewrite Split, SplitB.
    unfold Two_d_fix.
    rewrite SplitA, SplitB.
    apply (FPSound stmt2 B eqB RB OB (g (Fix stmt1 A eqA RA OA f f_ass))
    (g_ass (Fix stmt1 A eqA RA OA f f_ass))).
Qed.

Theorem Two_d_FPLeast (AB:Type) (eqAB RAB: AB -> AB -> Prop) (OAB:Two_d_orderassumption AB eqAB RAB) (h: AB -> AB) (F_ass: Two_d_functionassumption AB eqAB RAB OAB h):
forall x, eqAB (h x) x -> RAB (Two_d_fix AB eqAB RAB OAB h F_ass) x.
Proof.
  intros;apply L1.
  pose proof classic (RA (projA x) (projA (Two_d_fix AB eqAB RAB OAB h F_ass))) as H0;destruct H0.
  - right;split.
    + unfold Two_d_fix. rewrite SplitA. 
      rewrite L2 in H. destruct H.
      rewrite <- (CombineAB x) in H.
      rewrite Split in H.
      repeat rewrite SplitA in H.
      apply FPLeast. auto.
    + split;eauto.
      rewrite L2 in H;destruct H.
      pose proof FPLeast stmt2 B eqB RB OB (g (projA (Two_d_fix AB eqAB RAB OAB h F_ass))) (g_ass (projA (Two_d_fix AB eqAB RAB OAB h F_ass))) (projB x).
      unfold Two_d_fix. rewrite SplitB.
      unfold Two_d_fix in H2,H0;rewrite SplitA in H2,H0.
      apply H2. clear H2.
      rewrite Split,SplitA in H.
      rewrite Split,SplitB in H1.
      pose proof POA. destruct H2.
      pose proof FPLeast stmt1 A eqA RA OA f f_ass (projA x) H.
      assert (eqA (Fix stmt1 A eqA RA OA f f_ass) (projA x)).
      {apply PO_AntiSymmetric_Setoid;eauto. }
      clear H2 H0 PO_AntiSymmetric_Setoid PO_Reflexive_Setoid PO_Transitive.
      pose proof EB. destruct H0.
      eapply Equivalence_Transitive;[|apply H1].
      apply Proper_g;auto.
   - left;split. 
     rewrite L2 in H. destruct H.
     rewrite Split,SplitA in H.
     pose proof FPLeast stmt1 A eqA RA OA f f_ass (projA x) H.
     + unfold Two_d_fix. rewrite SplitA;auto.
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

