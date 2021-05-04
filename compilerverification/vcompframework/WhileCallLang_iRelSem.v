Require Import ZArith.
Require Import List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import VCF.Coqlib.
Require Import VCF.KnasterTarski.
Require Import VCF.GeneralDomain.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.BinRelDomain.
Require Import VCF.InfSem.
Require Import VCF.InfBinRelDomain.
Require Import VCF.WhileCallLang.

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
  solve_mono BinRel_solve_mono.
  rewrite H.
  reflexivity.
Qed.

Fixpoint ceval (c: com) (callee: func_name -> InfSem (state -> state -> Prop) (state -> Prop)): InfSem (state -> state -> Prop) (state -> Prop) :=
  match c with
  | CSkip => iRel.id
  | CAss a1 a2 =>
      {|
        fin_cases :=
          fun st1 st2 =>
            st2 (aeval a1 st1) = aeval a2 st1 /\
            forall l, aeval a1 st1 <> l -> st1 l = st2 l;
          inf_cases :=
            Sets.empty
      |}
  | CSeq c1 c2 => iRel.concat (ceval c1 callee) (ceval c2 callee)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1 callee) (ceval c2 callee)
  | CWhile b c => loop_sem (beval b) (ceval c callee)
  | CCall f => callee f
  end.

Definition single_binrel {A} (a0: A) (R: InfSem (state -> state -> Prop) (state -> Prop)): A -> InfSem (state -> state -> Prop) (state -> Prop) :=
  fun a =>
    {|
        fin_cases := fun b c => a = a0 /\ fin_cases R b c;
        inf_cases := fun b => a = a0 /\ inf_cases R b;
    |}.

Definition feval (fc: func_name * com) (callee: func_name -> InfSem (state -> state -> Prop) (state -> Prop)): func_name -> InfSem (state -> state -> Prop) (state -> Prop) :=
  match fc with
  | (f, c) => single_binrel f (ceval c callee)
  end.

Definition peval_pre (p: prog) (callee: func_name -> InfSem (state -> state -> Prop) (state -> Prop)):=
  fold_right Domain_union Domain_empty (map (fun fc => feval fc callee) p).

Fixpoint peval (p: prog): func_name -> InfSem (state -> state -> Prop) (state -> Prop) :=
  KT_fix_l (peval_pre p).

(***********************************************************)

Record partial_prog_denote: Type := {
  defined_funcs: func_name -> Prop;
  func_nodup: Prop;
  partial_sem: (func_name -> InfSem (state -> state -> Prop) (state -> Prop)) ->
               (func_name -> InfSem (state -> state -> Prop) (state -> Prop));
}.

Record partial_prog_denote_equiv (d1 d2: partial_prog_denote): Prop := {
  defined_funcs_equiv: forall f,
    defined_funcs d1 f <-> defined_funcs d2 f;
  func_nodup_equiv:
    func_nodup d1 <-> func_nodup d2;
  partial_sem_equiv:
    func_nodup d1 ->
    Domain_R' (partial_sem d1) (partial_sem d2)
}.

Definition partial_peval (p: list (func_name * com)): partial_prog_denote := {|
  defined_funcs := fun f => In f (map fst p);
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

Lemma separate_compile_defined_funcs: forall p1 p2: list (func_name * com),
  forall f, (In f (map fst (p1 ++ p2))) <->
            Sets.union
              (fun f => In f (map fst p1))
              (fun f => In f (map fst p2))
              f.
Proof.
  intros.
  unfold_SETS_tac idtac.
  rewrite map_app.
  rewrite in_app_iff.
  tauto.
Qed.

Lemma separate_compile_func_nodup: forall p1 p2: list (func_name * com),
  NoDup (map fst (p1 ++ p2)) <->
  NoDup (map fst p1) /\ NoDup (map fst p2) /\
    Sets.equiv
      (Sets.intersect
              (fun f => In f (map fst p1))
              (fun f => In f (map fst p2)))
      (Sets.empty).
Proof.
  intros.
  unfold_SETS_tac idtac.
  rewrite map_app.
  set (l1 := map fst p1).
  set (l2 := map fst p2).
  clearbody l1 l2; clear p1 p2.
  apply NoDup_app_iff.
Qed.

(*
Lemma partial_sem_BW_fix2: forall p1 p2 extern_sem,
  let f1 d1 d2 := peval_pre p1 (Sets.union extern_sem (Sets.union d1 d2)) in
  let f2 d1 d2 := peval_pre p2 (Sets.union extern_sem (Sets.union d1 d2)) in
  Sets.equiv
    (BW_fix (fun sem => peval_pre (p1 ++ p2) (Sets.union extern_sem sem)))
    (union_pair (BW_fix2 f1 f2)).
Proof.
  intros.
Admitted.

Lemma separate_compile_partial_sem: forall p1 p2 extern_sem,
  Sets.equiv
    (BW_fix (fun sem => peval_pre (p1 ++ p2) (Sets.union extern_sem sem)))
    (union_pair
       (BW_fix2
          (fun _ sem2 =>
             BW_fix (fun sem => peval_pre p1 (Sets.union (Sets.union extern_sem sem2) sem)))
          (fun sem1 _ =>
             BW_fix (fun sem => peval_pre p2 (Sets.union (Sets.union extern_sem sem1) sem))))).
Proof.
  intros.
  rewrite partial_sem_BW_fix2.
  set (f1 d1 d2 := peval_pre p1 (Sets.union extern_sem (Sets.union d1 d2))).
  set (f2 d1 d2 := peval_pre p2 (Sets.union extern_sem (Sets.union d1 d2))).
  apply union_pair_equiv.
  rewrite two_dimensional_fix_coincide.
Admitted.
 *)

Theorem separate_compile: forall p1 p2,
  partial_prog_denote_equiv
    (partial_peval (p1 ++ p2))
    (partial_prog_denote_compose (partial_peval p1) (partial_peval p2)).
Proof.
  intros.
  constructor.
  + apply separate_compile_defined_funcs.
  + apply separate_compile_func_nodup.
  + intros.
    intros extern_sem.
(*    apply separate_compile_partial_sem.
Qed.*)
Admitted.
