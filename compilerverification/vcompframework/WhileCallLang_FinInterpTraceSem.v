Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import VCF.KnasterTarski.
Require Import VCF.WhileCallLang.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.FinTraceRelDomain.
Require Import VCF.TraceInterp.

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

Definition sys_func_name := positive.
Definition custom_func_name := positive.

Inductive event: Type :=
| SysCall (fid: sys_func_name) (arg: Z)
| CustomCall (fid: custom_func_name) (st1 st2: state).

Definition if_sem
  (cond: state -> Prop)
  (then_branch else_branch: state -> list event -> state -> Prop)
  : state -> list event -> state -> Prop
:=
  Sets.union
    (TrRel.concat (TrRel.test cond nil) then_branch)
    (TrRel.concat (TrRel.test (Sets.complement cond) nil) else_branch).

Definition loop_sem_CL:
  @CompleteLattice_Setoid
    (state -> list event -> state -> Prop)
    Sets.included
    Sets.equiv
    Sets.omega_union
:= SETS_included_CL.

Local Existing Instance loop_sem_CL.

Definition loop_sem (cond: state -> Prop) (loop_body: state -> list event -> state -> Prop):
  state -> list event -> state -> Prop :=
  KT_fix_l
    (fun sem =>
       Sets.union
         (TrRel.concat
           (TrRel.test cond nil)
           (TrRel.concat loop_body sem))
         (TrRel.test (Sets.complement cond) nil)).

Fixpoint ceval (c: com): state -> list event -> state -> Prop :=
  match c with
  | CSkip => TrRel.id
  | CAss a1 a2 =>
      fun st1 tr st2 =>
        st2 (aeval a1 st1) = aeval a2 st1 /\
        (forall l, aeval a1 st1 <> l -> st1 l = st2 l) /\
        tr = nil
  | CSeq c1 c2 => TrRel.concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1) (ceval c2)
  | CWhile b c => loop_sem (beval b) (ceval c)
  | CCall f => match f with
               | Zneg fid => fun st1 tr st2 => st1 = st2 /\ tr = SysCall fid (st1 0%Z) :: nil
               | Zpos fid => fun st1 tr st2 => tr = CustomCall fid st1 st2 :: nil
               | _ => Sets.empty
               end
  end.

Inductive den2eh (d: custom_func_name -> state -> list event -> state -> Prop): event -> list event -> Prop :=
| Build_den2eh fid st1 tr st2:
    d fid st1 tr st2 ->
    den2eh d (CustomCall fid st1 st2) tr.

Definition eh2den (eh: event -> list event -> Prop): custom_func_name -> state -> list event -> state -> Prop :=
  fun fid st1 tr st2 => eh (CustomCall fid st1 st2) tr.

Inductive is_custom_call: event -> Prop :=
| CustomCall_is_custom_call: forall fid st1 st2,
    is_custom_call (CustomCall fid st1 st2).

Definition single_trace_rel {A B C T} (a0: A) (R: B -> T -> C -> Prop): A -> B -> T -> C -> Prop :=
  fun a b tr c => a = a0 /\ R b tr c.

Definition feval (fc: func_name * com): custom_func_name -> state -> list event -> state -> Prop :=
  match fc with
  | (Zpos fid, c) => single_trace_rel fid (ceval c)
  | _ => Sets.empty
  end.

Definition peval_pre (p: prog) :=
  den2eh (fold_right Sets.union Sets.empty (map (fun fc => feval fc) p)).

Definition prog_sem_CL:
  @CompleteLattice_Setoid
    (event -> list event -> Prop)
    Sets.included
    Sets.equiv
    Sets.omega_union
:= SETS_included_CL.

Existing Instance prog_sem_CL.

Fixpoint peval (p: prog): custom_func_name -> state -> list event -> state -> Prop :=
  eh2den (KT_fix_l (refine_fin_fin (peval_pre p) is_custom_call)).

(***********************************************************)

Record partial_prog_denote: Type := {
  defined_funcs: custom_func_name -> Prop;
  func_nodup: Prop;
  partial_sem: custom_func_name -> state -> list event -> state -> Prop;
}.

Record partial_prog_denote_equiv (d1 d2: partial_prog_denote): Prop := {
  defined_funcs_equiv: forall f,
    defined_funcs d1 f <-> defined_funcs d2 f;
  func_nodup_equiv:
    func_nodup d1 <-> func_nodup d2;
  partial_sem_equiv: Sets.equiv (partial_sem d1) (partial_sem d2)
}.

Inductive is_custom_callx (X: custom_func_name -> Prop): event -> Prop :=
| CustomCall_is_custom_callx: forall fid st1 st2,
    X fid ->
    is_custom_callx X (CustomCall fid st1 st2).

Definition partial_peval (p: list (func_name * com)): partial_prog_denote := {|
  defined_funcs := fun f => exists c, In (Zpos f, c) p;
  func_nodup := NoDup (map fst p);
  partial_sem := eh2den (KT_fix_l (refine_fin_fin (peval_pre p) (is_custom_callx (fun f => exists c, In (Zpos f, c) p))))
|}.

Definition partial_prog_denote_compose (d1 d2: partial_prog_denote): partial_prog_denote := {|
  defined_funcs := Sets.union (defined_funcs d1) (defined_funcs d2);
  func_nodup := func_nodup d1 /\
                func_nodup d2 /\
                Sets.equiv
                  (Sets.intersect (defined_funcs d1) (defined_funcs d2))
                  Sets.empty;
  partial_sem := eh2den
                   (KT_fix_l (refine_fin_fin (Sets.union (den2eh (partial_sem d1)) (den2eh (partial_sem d2))) (is_custom_callx (Sets.union (defined_funcs d1) (defined_funcs d2)))))
|}.

Theorem separate_compile: forall p1 p2,
  partial_prog_denote_equiv
    (partial_peval (p1 ++ p2))
    (partial_prog_denote_compose (partial_peval p1) (partial_peval p2)).
Proof.
Admitted.

