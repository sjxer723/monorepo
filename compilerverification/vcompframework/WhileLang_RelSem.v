Require Import ZArith.
Require Import VCF.Sem.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.BinRelDomain.
Require Import VCF.KnasterTarski.
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
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  Sets.union
    (Rel.concat (Rel.test cond) then_branch)
    (Rel.concat (Rel.test (Sets.complement cond)) else_branch).

Definition loop_sem_CL:
  @CompleteLattice_Setoid
    (state -> state -> Prop)
    Sets.included
    Sets.equiv
    Sets.omega_union
:= SETS_included_CL.

Local Existing Instance loop_sem_CL.

Definition loop_sem (cond: state -> Prop) (loop_body: state -> state -> Prop):
  state -> state -> Prop :=
  KT_fix_l
    (fun sem =>
       Sets.union
         (Rel.concat
           (Rel.test cond)
           (Rel.concat loop_body sem))
         (Rel.test (Sets.complement cond))).

Lemma loop_sem_recur:
  forall cond loop_body,
    Sets.equiv
      (loop_sem cond loop_body)
      (Sets.union
         (Rel.concat
           (Rel.test cond)
           (Rel.concat loop_body (loop_sem cond loop_body)))
         (Rel.test (Sets.complement cond))).
Proof.
  intros.
  unfold loop_sem.
  match goal with
  | |- Sets.equiv (KT_fix_l ?F) _ =>
    pose proof KnasterTarski_fixpoint_theorem_l F as H; apply H; clear H
  end.
  hnf; intros.
  solve_mono BinRel_solve_mono.
Qed.

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => Rel.id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => Rel.concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1) (ceval c2)
  | CWhile b c => loop_sem (beval b) (ceval c)
  end.


