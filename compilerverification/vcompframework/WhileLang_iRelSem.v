Require Import ZArith.
Require Import VCF.KnasterTarski.
Require Import VCF.GeneralDomain.
Require Import VCF.Sem.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.BinRelDomain.
Require Import VCF.InfSem.
Require Import VCF.InfBinRelDomain.
Require Import VCF.WhileLang.

Definition state := var -> Z.
Definition constant_func {A: Type} (c: Z): A -> Z := fun _ => c.
Definition query_var (X: var): state -> Z := fun st => st X.

Fixpoint aeval (a : aexp) : state -> Z :=
  match a with
  | ANum n => constant_func n
  | AId X => query_var X
  | APlus a1 a2 => (aeval a1 + aeval a2)%Func
  | AMinus a1 a2  => (aeval a1 - aeval a2)%Func
  | AMult a1 a2 => (aeval a1 * aeval a2)%Func
  end.

Fixpoint beval (b : bexp) : state -> Prop :=
  match b with
  | BTrue       => Sets.full
  | BFalse      => Sets.empty
  | BEq a1 a2   => ZFunc.test_eq (aeval a1) (aeval a2)
  | BLe a1 a2   => ZFunc.test_le (aeval a1) (aeval a2)
  | BNot b1     => Sets.complement (beval b1)
  | BAnd b1 b2  => Sets.intersect (beval b1 ) (beval b2)
  end.

Definition if_sem
  (cond: state -> Prop)
  (then_branch else_branch: InfSem (state -> state -> Prop) (state -> Prop))
  : InfSem (state -> state -> Prop) (state -> Prop)
:=
  Domain_union
    (iRel.concat (iRel.test cond) then_branch)
    (iRel.concat (iRel.test (Sets.complement cond)) else_branch).

Definition loop_sem (cond: state -> Prop) (loop_body: InfSem (state -> state -> Prop) (state -> Prop)):
  InfSem (state -> state -> Prop) (state -> Prop) :=
  KT_fix_l
    (fun sem =>
       Domain_union
         (iRel.concat
           (iRel.test cond)
           (iRel.concat loop_body sem))
         (iRel.test (Sets.complement cond))).

Lemma loop_sem_recur:
  forall cond loop_body,
    Domain_R'
      (loop_sem cond loop_body)
      (Domain_union
         (iRel.concat
           (iRel.test cond)
           (iRel.concat loop_body (loop_sem cond loop_body)))
         (iRel.test (Sets.complement cond))).
Proof.
  intros.
  unfold loop_sem.
  match goal with
  | |- Domain_R' (KT_fix_l ?F) _ =>
    pose proof KnasterTarski_fixpoint_theorem_l F as H; apply H; clear H
  end.
  hnf; intros.
(*
    solve_mono BinRel_solve_mono.
  + hnf; intros.
    unfold Basics.compose.
    solve_cont BinRel_solve_cont.
Qed.
*)
Admitted.

Fixpoint ceval (c: com): InfSem (state -> state -> Prop) (state -> Prop) :=
  match c with
  | CSkip => iRel.id
  | CAss X E =>
      {|
        fin_cases :=
          fun st1 st2 =>
          st2 X = aeval E st1 /\
          forall Y, X <> Y -> st1 Y = st2 Y;
        inf_cases :=
          Sets.empty
      |}
  | CSeq c1 c2 => iRel.concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1) (ceval c2)
  | CWhile b c => loop_sem (beval b) (ceval c)
  end.
