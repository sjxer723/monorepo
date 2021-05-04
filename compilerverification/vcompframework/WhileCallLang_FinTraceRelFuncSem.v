Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import VCF.PairConstructors.
Require Import VCF.WhileCallLang.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.FinTraceRelDomain.
Require Import VCF.KnasterTarski.

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

Fixpoint ceval (c: com) (callee: func_name -> state -> list event -> state -> Prop): state -> list event -> state -> Prop :=
  match c with
  | CSkip => TrRel.id
  | CAss a1 a2 =>
      fun st1 tr st2 =>
        st2 (aeval a1 st1) = aeval a2 st1 /\
        (forall l, aeval a1 st1 <> l -> st1 l = st2 l) /\
        tr = nil
  | CSeq c1 c2 => TrRel.concat (ceval c1 callee) (ceval c2 callee)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1 callee) (ceval c2 callee)
  | CWhile b c => loop_sem (beval b) (ceval c callee)
  | CCall f => match f with
               | Zneg fid => fun st1 tr st2 => st1 = st2 /\ tr = (fid, st1 0%Z) :: nil (* sys call *)
               | _ => callee f                                                    (* internal call *)
               end
  end.

Definition single_trace_rel {A B C T} (a0: A) (R: B -> T -> C -> Prop): A -> B -> T -> C -> Prop :=
  fun a b tr c => a = a0 /\ R b tr c.

Definition feval (fc: func_name * com) (callee: func_name -> state -> list event -> state -> Prop): func_name -> state -> list event -> state -> Prop :=
  match fc with
  | (f, c) => single_trace_rel f (ceval c callee)
  end.

Definition peval_pre (p: prog) (callee: func_name -> state -> list event -> state -> Prop):=
  fold_right Sets.union Sets.empty (map (fun fc => feval fc callee) p).

Definition prog_sem_CL:
  @CompleteLattice_Setoid
    (func_name -> state -> list event -> state -> Prop)
    Sets.included
    Sets.equiv
    Sets.omega_union
:= SETS_included_CL.

Existing Instance prog_sem_CL.

Fixpoint peval (p: prog): func_name -> state -> list event -> state -> Prop :=
  KT_fix_l (peval_pre p).

(***********************************************************)

Record partial_prog_denote: Type := {
  defined_funcs: func_name -> Prop;
  func_nodup: Prop;
  partial_sem: (func_name -> state -> list event -> state -> Prop) ->
               (func_name -> state -> list event -> state -> Prop);
}.

Record partial_prog_denote_equiv (d1 d2: partial_prog_denote): Prop := {
  defined_funcs_equiv: forall f,
    defined_funcs d1 f <-> defined_funcs d2 f;
  func_nodup_equiv:
    func_nodup d1 <-> func_nodup d2;
  partial_sem_equiv: Sets.equiv (partial_sem d1) (partial_sem d2)
}.

Definition partial_peval (p: list (func_name * com)): partial_prog_denote := {|
  defined_funcs := fun f => exists c, In (f, c) p;
  func_nodup := NoDup (map fst p);
  partial_sem := fun extern_sem =>
                   KT_fix_l (fun sem => peval_pre p (Sets.union extern_sem sem))
|}.

Definition union_pair {A: Type} {A_SETS: Sets.SETS A} (p: A * A): A :=
  Sets.union (fst p) (snd p).

Lemma union_pair_equiv: forall {A: Type} {A_SETS: Sets.SETS A} p1 p2,
  pair_rel2 Sets.equiv Sets.equiv p1 p2 -> Sets.equiv (union_pair p1) (union_pair p2).
Admitted.

Definition partial_prog_denote_compose (d1 d2: partial_prog_denote): partial_prog_denote := {|
  defined_funcs := Sets.union (defined_funcs d1) (defined_funcs d2);
  func_nodup := func_nodup d1 /\
                func_nodup d2 /\
                Sets.equiv
                  (Sets.intersect (defined_funcs d1) (defined_funcs d2))
                  Sets.empty;
  partial_sem := fun extern_sem =>
                   union_pair
                     (KT_fix2_l
                       (fun _ sem2 => partial_sem d1 (Sets.union extern_sem sem2))
                       (fun sem1 _ => partial_sem d2 (Sets.union extern_sem sem1)))
|}.

Theorem separate_compile: forall p1 p2,
  partial_prog_denote_equiv
    (partial_peval (p1 ++ p2))
    (partial_prog_denote_compose (partial_peval p1) (partial_peval p2)).
Proof.
Admitted.
