Require Import Basics.
Require Import VCF.KnasterTarski.
Require Import VCF.SetsDomain.
Require Import VCF.TraceGeneral.
Require Import VCF.FiniteDivergeTrace.

Definition fin_fin_CPO {A: Type}:
  @CompleteLattice_Setoid
    (list A -> list A -> Prop)
    Sets.included
    Sets.equiv
    Sets.omega_union
:= SETS_included_CL.

Existing Instance fin_fin_CPO.

Inductive fin_fin_gen {A: Type} (dom: A -> Prop) (mat: A -> list A -> Prop) (rel: list A -> list A -> Prop): list A -> list A -> Prop :=
| fin_fin_nil: fin_fin_gen dom mat rel nil nil
| fin_fin_skip: forall a l1 l2, ~ dom a -> rel l1 l2 -> fin_fin_gen dom mat rel (a :: l1) (a :: l2)
| fin_fin_step: forall a l l1 l2, dom a -> mat a l -> rel l1 l2 -> fin_fin_gen dom mat rel (a :: l1) (l ++ l2).

Definition interp_fin_fin {A: Type} (dom: A -> Prop) (mat: A -> list A -> Prop): list A -> list A -> Prop :=
  KT_fix_l (fin_fin_gen dom mat).
(*
Definition fin_inf_CPO {A: Type}:
  @CompletePartialOrder_Setoid
    (list A -> (nat -> A) -> Prop)
    (fun P Q => Sets.included Q P)
    Sets.equiv
    Sets.omega_intersect
    Sets.full
:= lift_CPO _ (lift_CPO _ Prop_forall_True_CPO).

Existing Instance fin_inf_CPO.

Inductive fin_inf_gen {A: Type} (dom: A -> Prop) (mat: A -> list A -> Prop) (rel: list A -> (nat -> A) -> Prop): list A -> (nat -> A) -> Prop :=
| fin_inf_skip: forall a l1 l2, ~ dom a -> rel l1 l2 -> fin_inf_gen dom mat rel (a :: l1) (natfunc_app (a::nil) l2)
| fin_inf_step: forall a l l1 l2, dom a -> mat a l -> rel l1 l2 -> fin_inf_gen dom mat rel (a :: l1) (natfunc_app l l2).

Definition interp_fin_inf {A: Type} (dom: A -> Prop) (mat: A -> list A -> Prop): list A -> (nat -> A) -> Prop :=
  BW_fix (fin_inf_gen dom mat).
*)
Definition inf_inf_CPO {A: Type}:
  @CompleteLattice_Setoid
    ((nat -> A) -> (nat -> A) -> Prop)
    (flip Sets.included)
    Sets.equiv
    Sets.omega_intersect
:= SETS_flip_included_CL.

Existing Instance inf_inf_CPO.

Inductive inf_inf_gen {A: Type} (dom: A -> Prop) (mat: A -> list A -> Prop) (rel: (nat -> A) -> (nat -> A) -> Prop): (nat -> A) -> (nat -> A) -> Prop :=
| inf_inf_skip: forall a l1 l2, ~ dom a -> rel l1 l2 -> inf_inf_gen dom mat rel (natfunc_app (a::nil) l1) (natfunc_app (a::nil) l2)
| inf_inf_step: forall a l l1 l2, dom a -> mat a l -> rel l1 l2 -> inf_inf_gen dom mat rel (natfunc_app (a::nil)  l1) (natfunc_app l l2).

Definition interp_inf_inf {A: Type} (dom: A -> Prop) (mat: A -> list A -> Prop): (nat -> A) -> (nat -> A) -> Prop :=
  KT_fix_l (inf_inf_gen dom mat).

Definition FDvg_Dvg_CPO {A B: Type}:
  @CompleteLattice_Setoid
    (FDvgTrace A B -> DvgTrace A B -> Prop)
    (flip Sets.included)
    Sets.equiv
    Sets.omega_intersect
:= SETS_flip_included_CL.

Existing Instance FDvg_Dvg_CPO.

Inductive FDvg_Dvg_gen
            {A B: Type}
            (domA: A -> Prop) (matA: A -> list A -> Prop)
            (domB: B -> Prop) (matB: B -> DvgTrace A B -> Prop)
            (rel: FDvgTrace A B -> DvgTrace A B -> Prop): FDvgTrace A B -> DvgTrace A B -> Prop :=
| FDvg_Dvg_nil_skip: forall b,
    ~ domB b ->
    FDvg_Dvg_gen domA matA domB matB rel
      {| head_events := nil; tail_event := b |}
      (Finite_Diverge {| head_events := nil; tail_event := b |})
| FDvg_Dvg_nil_step: forall b tr,
    domB b ->
    matB b tr ->
    FDvg_Dvg_gen domA matA domB matB rel
      {| head_events := nil; tail_event := b |}
      tr
| FDvg_Dvg_skip: forall a tr1 tr2,
    ~ domA a ->
    rel tr1 tr2 ->
    FDvg_Dvg_gen domA matA domB matB rel
      (fd_trace_app (a::nil) tr1) (diverge_trace_app (a::nil) tr2)
| FDvg_Dvg_step: forall a l tr1 tr2,
    domA a ->
    matA a l ->
    rel tr1 tr2 ->
    FDvg_Dvg_gen domA matA domB matB rel
      (fd_trace_app (a::nil) tr1) (diverge_trace_app l tr2).

Definition interp_FDvg_Dvg
             {A B: Type}
             (domA: A -> Prop) (matA: A -> list A -> Prop)
             (domB: B -> Prop) (matB: B -> DvgTrace A B -> Prop): FDvgTrace A B -> DvgTrace A B -> Prop :=
  KT_fix_l (FDvg_Dvg_gen domA matA domB matB).

(*********************)

Inductive refine_fin_fin {A} (eh1: A -> list A -> Prop) (dom: A -> Prop) (eh2: A -> list A -> Prop): A -> list A -> Prop :=
| Build_refine_fin_fin: forall a l l',
    eh1 a l ->
    interp_fin_fin dom eh2 l l' ->
    refine_fin_fin eh1 dom eh2 a l'.

Inductive refine_inf_Dvg {A B} (eh1: B -> (nat -> A) -> Prop) (dom: A -> Prop) (eh2: A -> list A -> Prop): B -> DvgTrace A B  -> Prop :=
| Build_refine_inf_inf: forall b tr tr',
    eh1 b tr ->
    interp_inf_inf dom eh2 tr tr' ->
    refine_inf_Dvg eh1 dom eh2 b (Infinite_Diverge tr').

Inductive refine_Dvg_Dvg
          {A B}
          (eh1: B -> DvgTrace A B -> Prop)                 
          (domA: A -> Prop) (domB: B -> Prop)
          (eh2A: A -> list A -> Prop) (eh2B: B -> DvgTrace A B  -> Prop): B -> DvgTrace A B  -> Prop :=
| Build_refine_Finite_Dvg_Dvg: forall b tr tr',
    eh1 b (Finite_Diverge tr) ->
    interp_FDvg_Dvg domA eh2A domB eh2B tr tr' ->
    refine_Dvg_Dvg eh1 domA domB eh2A eh2B b tr'
| Build_refine_Infinite_Dvg_Dvg: forall b tr tr',
    eh1 b (Infinite_Diverge tr) ->
    interp_inf_inf domA eh2A tr tr' ->
    refine_Dvg_Dvg eh1 domA domB eh2A eh2B b (Infinite_Diverge tr').
