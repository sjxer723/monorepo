Require Import VCF.Sem.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.BinRelDomain.
Require Import VCF.Coqlib.
Require Import VCF.KnasterTarski.
Require Import ZArith.
Require Import List.

Local Open Scope Z.

Definition var: Type := nat.

Inductive unop: Type :=
  | BNot.

Inductive binop: Type :=
  | APlus
  | AMinus
  | AMult
  | BEq
  | BLe
  | BAnd.

Inductive com : Type :=
  | CSkip
  | CAssConst (X: var) (n : Z)
  | CAssVar (X: var) (Y : var)
  | CAssUnop (X: var) (op: unop) (Y : var)
  | CAssBinop (X: var) (op: binop) (Y : var) (Z : var)
  | CSeq (c1 c2 : com)
  | CIf (X : var) (c1 c2 : com)
  | CWhile (X : var) (c : com).

Definition unop_sem (op: unop): Z -> Z :=
  match op with
  | BNot => fun x => if Z.eqb x 0 then 1 else 0
  end.

Definition binop_sem (op: binop): Z -> Z -> Z :=
  match op with
  | APlus => Z.add
  | AMinus => Z.sub
  | AMult => Z.mul
  | BEq => fun x y => if Z.eqb x y then 1 else 0
  | BLe => fun x y => if Z.leb x y then 1 else 0
  | BAnd => fun x y => if andb (Z.eqb x 1) (Z.eqb y 1) then 1 else 0
  end.

Definition state := var -> Z.

Definition var_true_sets (X: var) : state -> Prop :=
  fun st => st X <> 0.

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

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => Rel.id
  | CAssConst X n =>
      fun st1 st2 =>
        st2 X = n /\
        forall V, X <> V -> st1 V = st2 V
  | CAssVar X Y =>
      fun st1 st2 =>
        st2 X = st1 Y /\
        forall V, X <> V -> st1 V = st2 V
  | CAssUnop X op Y =>
      fun st1 st2 =>
        st2 X = unop_sem op (st1 Y) /\
        forall V, X <> V -> st1 V = st2 V
  | CAssBinop X op Y Z =>
      fun st1 st2 =>
        st2 X = binop_sem op (st1 Y) (st1 Z) /\
        forall V, X <> V -> st1 V = st2 V
  | CSeq c1 c2 => Rel.concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem (var_true_sets b) (ceval c1) (ceval c2)
  | CWhile b c => loop_sem (var_true_sets b) (ceval c)
  end.

Lemma ceval_fold_right_CSeq: forall cs c,
  ceval (fold_right CSeq c cs) = fold_right Rel.concat (ceval c) (map ceval cs).
Proof.
  intros.
  apply fold_right_map.
  intros.
  simpl.
  auto.
Qed.

Lemma ceval_fold_left_CSeq: forall cs c,
  ceval (fold_left CSeq cs c) = fold_left Rel.concat (map ceval cs) (ceval c).
Proof.
  intros.
  apply fold_left_map.
  intros.
  simpl.
  auto.
Qed.
