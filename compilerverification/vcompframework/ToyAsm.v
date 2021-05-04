Require Import VCF.Sem.

Definition var: Type := nat.

Definition label: Type := nat.

Inductive uop: Type :=
  | BNot.

Inductive binop: Type :=
  | APlus
  | AMinus
  | Amult
  | BEq
  | BLe.

Inductive com : Type :=
  | CAssVar (X: var) (Y : var)
  | CAssUnop (X: var) (op: uop) (Y : var)
  | CJump (l: label)
  | CCondJump (X: var) (l: label).

Definition prog: Type := list (nat * com).

