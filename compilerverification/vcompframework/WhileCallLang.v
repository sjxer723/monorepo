Require Import VCF.Sem.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.BinRelDomain.
Require Import ZArith.

Definition func_name: Type := Z.

Inductive aexp : Type :=
  | ANum (n : Z)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADeref (a1: aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Type :=
  | CSkip
  | CAss (a1 a2 : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CCall (f: func_name).

Definition prog : Type := list ((func_name * com)%type).

