Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import VCF.PairConstructors.
Require Import VCF.WhileCallLang.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.InfSem.
Require Import VCF.FiniteDivergeTrace.
Require Import VCF.FinTraceRelDomain.
Require Import VCF.InfTraceRelDomain.
Require Import VCF.KnasterTarski.
Require Import VCF.GeneralDomain.

Definition state := Z -> Z.
Definition constant_func {A: Type} (c: Z): A -> Z := fun _ => c.

Fixpoint aeval (a : aexp) : state -> Z :=
  match a with
  | ANum n => constant_func n
  | APlus a1 a2 => (aeval a1 + aeval a2)%Func
  | AMinus a1 a2  => (aeval a1 - aeval a2)%Func
  | AMult a1 a2 => (aeval a1 * aeval a2)%Func
  | ADeref a1 => fun st => st ((aeval a1) st)
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

Definition event: Type := positive * Z.

Definition if_sem
  (cond: state -> Prop)
  (then_branch else_branch: InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop))
  : InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop)
:=
  Domain_union
    (iTrRel.concat (iTrRel.test cond nil) then_branch)
    (iTrRel.concat (iTrRel.test (Sets.complement cond) nil) else_branch).

Definition loop_sem (cond: state -> Prop) (loop_body: InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop)):
  InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop) :=
  KT_fix_l
    (fun sem =>
       Domain_union
         (iTrRel.concat
           (iTrRel.test cond nil)
           (iTrRel.concat loop_body sem))
         (iTrRel.test (Sets.complement cond) nil)).

Lemma loop_sem_recur:
  forall cond loop_body,
    Domain_R'
      (loop_sem cond loop_body)
      (Domain_union
         (iTrRel.concat
           (iTrRel.test cond nil)
           (iTrRel.concat loop_body (loop_sem cond loop_body)))
         (iTrRel.test (Sets.complement cond) nil)).
Proof.
  intros.
  unfold loop_sem.
  match goal with
  | |- Domain_R' (KT_fix_l ?F) _ =>
    pose proof KnasterTarski_fixpoint_theorem_l F as H; apply H; clear H
  end.
  hnf; intros.
  rewrite H.
  reflexivity.
Qed.

Fixpoint ceval (c: com) (callee: func_name -> InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop)): InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop) :=
  match c with
  | CSkip => iTrRel.id
  | CAss a1 a2 =>
      {|
        fin_cases :=
          fun st1 tr st2 =>
            st2 (aeval a1 st1) = aeval a2 st1 /\
            (forall l, aeval a1 st1 <> l -> st1 l = st2 l) /\
            tr = nil;
          inf_cases :=
            Sets.empty
      |}
  | CSeq c1 c2 => iTrRel.concat (ceval c1 callee) (ceval c2 callee)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1 callee) (ceval c2 callee)
  | CWhile b c => loop_sem (beval b) (ceval c callee)
  | CCall f => match f with
               | Zneg fid =>
                   {|
                     fin_cases := fun st1 tr st2 => st1 = st2 /\ tr = (fid, st1 0%Z) :: nil;
                     inf_cases := Sets.empty
                   |}
               | _ => callee f
               end
  end.

Definition single_binrel {A} (a0: A) (R: InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop)): A -> InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop) :=
  fun a =>
    {|
        fin_cases := fun b tr c => a = a0 /\ fin_cases R b tr c;
        inf_cases := fun b tr=> a = a0 /\ inf_cases R b tr;
    |}.

Definition feval (fc: func_name * com) (callee: func_name -> InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop)): func_name -> InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop) :=
  match fc with
  | (f, c) => single_binrel f (ceval c callee)
  end.

Definition peval_pre (p: prog) (callee: func_name -> InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop)):=
  fold_right Domain_union Domain_empty (map (fun fc => feval fc callee) p).

Fixpoint peval (p: prog): func_name -> InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop) :=
  KT_fix_l (peval_pre p).

(***********************************************************)

Record partial_prog_denote: Type := {
  defined_funcs: func_name -> Prop;
  func_nodup: Prop;
  partial_sem: (func_name -> InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop)) ->
               (func_name -> InfSem (state -> list event -> state -> Prop) (state -> FDvgTrace event unit -> Prop));
}.

Record partial_prog_denote_equiv (d1 d2: partial_prog_denote): Prop := {
  defined_funcs_equiv: forall f,
    defined_funcs d1 f <-> defined_funcs d2 f;
  func_nodup_equiv:
    func_nodup d1 <-> func_nodup d2;
  partial_sem_equiv: Domain_R' (partial_sem d1) (partial_sem d2)
}.

Definition partial_peval (p: list (func_name * com)): partial_prog_denote := {|
  defined_funcs := fun f => exists c, In (f, c) p;
  func_nodup := NoDup (map fst p);
  partial_sem := fun extern_sem => KT_fix_l (fun sem => peval_pre p (Domain_union extern_sem sem)) 
|}.

Definition union_pair {A: Type} {CLA: CL_Domain A} {UnionA: Union_Domain A} (p: A * A): A :=
  Domain_union (fst p) (snd p).

Lemma union_pair_equiv: forall {A: Type} {CLA: CL_Domain A} {UnionA: Union_Domain A} p1 p2,
  Domain_R' p1 p2 -> Domain_R' (union_pair p1) (union_pair p2).
Admitted.

Definition partial_prog_denote_compose (d1 d2: partial_prog_denote): partial_prog_denote := {|
  defined_funcs := Sets.union (defined_funcs d1) (defined_funcs d2);
  func_nodup := func_nodup d1 /\ func_nodup d2 /\
                Sets.equiv (Sets.intersect (defined_funcs d1) (defined_funcs d2)) Sets.empty;
  partial_sem := fun extern_sem =>
                   union_pair
                     (KT_fix2_l
                       (fun _ sem2 => partial_sem d1 (Domain_union extern_sem sem2))
                       (fun sem1 _ => partial_sem d2 (Domain_union extern_sem sem1)))
|}.

Theorem separate_compile: forall p1 p2,
  partial_prog_denote_equiv
    (partial_peval (p1 ++ p2))
    (partial_prog_denote_compose (partial_peval p1) (partial_peval p2)).
Proof.
Admitted.

