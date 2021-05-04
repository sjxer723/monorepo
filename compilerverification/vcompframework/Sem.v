Require Import Equivalence.
Require Import Relations.
Require Import Morphisms.
Require Import RelationPairs.

Record ProgLang: Type :=
{
  expr: Type
}.

Record Domain: Type :=
{
  domain: Type;
  deq: domain -> domain -> Prop;
  deq_equiv: Equivalence deq;
}.

Record DSem (P: ProgLang) (D: Domain): Type :=
{
  denote: P.(expr) -> D.(domain)
}.

Arguments denote {_} {_} (_) (_).

Record Compiler (P P': ProgLang): Type :=
{
  compile: P.(expr) -> P'.(expr);
}.

Record domain_rel (D1 D2: Domain): Type :=
{
  rel: D1.(domain) -> D2.(domain) -> Prop;
  rel_wd: forall d11 d12 d21 d22, D1.(deq) d11 d12 -> D2.(deq) d21 d22 -> rel d11 d21 -> rel d12 d22;
}.

Arguments rel {_} {_} (_) (_) (_).

Record part_of_prog (P P': ProgLang): Type :=
{
  prog_inj: P.(expr) -> P'.(expr);
  prog_inj_is_injection: forall e1 e2, prog_inj e1 = prog_inj e2 -> e1 = e2;
}.

Record domain_refine (D1 D2: Domain): Type :=
{
  refine_rel: domain_rel D1 D2;
  refine_is_refinement: forall d11 d12 d21 d22, D1.(deq) d11 d12 -> refine_rel.(rel) d11 d21 -> refine_rel.(rel) d12 d22 -> D2.(deq) d21 d22;
}.

Fixpoint Domain_Function (D: Domain) (n: nat): Type :=
  match n with
  | O => D.(domain)
  | S n0 => D.(domain) -> Domain_Function D n0
  end.

Definition Domain_Prod (D1 D2: Domain): Domain :=
  Build_Domain
    (D1.(domain) * D2.(domain))
    (RelProd D1.(deq) D2.(deq))
    (RelProd_Equivalence _ _ D1.(deq_equiv) D2.(deq_equiv)).

Record State: Type :=
{
  state: Type;
}.  

Record Trace: Type :=
{
  trace: Type;
}.

Record SSSem (P: ProgLang) (P': ProgLang) (St: State) (Tr: Trace): Type :=
{
  interp: P.(expr) -> P'.(expr);
  step: P'.(expr) -> St.(state) -> Tr.(trace) -> P'.(expr) -> St.(state) -> Prop;
  halt: P'.(expr) -> St.(state) -> Prop;
  step_halt_cover: forall e s, halt e s \/ exists tr e' s', step e s tr e' s';
  step_halt_conflict: forall e s tr e' s', halt e s -> step e s tr e' s' -> False;
}.

Arguments interp {_} {_} {_} {_} (_) (_).
Arguments step {_} {_} {_} {_} (_) (_) (_) (_) (_) (_).
Arguments halt {_} {_} {_} {_} (_) (_) (_).

Definition DSem_refine {P D1 D2} (Sem1: DSem P D1) (Sem2: DSem P D2) (R: D1.(domain) -> D2.(domain) -> Prop): Prop :=
  forall e, R (Sem1.(denote) e) (Sem2.(denote) e).

Inductive multi_step {P P' St Tr} (Sem: SSSem P P' St Tr):
  P'.(expr) -> St.(state) -> list Tr.(trace) -> P'.(expr) -> St.(state) -> Prop :=
| multi_step_nil: forall e s,
    Sem.(multi_step) e s nil e s
| multi_step_cons: forall e1 s1 e2 s2 e3 s3 tr0 trs,
    Sem.(step) e1 s1 tr0 e2 s2 ->
    Sem.(multi_step) e2 s2 trs e3 s3 ->
    Sem.(multi_step) e1 s1 (tr0 :: trs) e3 s3.

Inductive omega_step {P P' St Tr} (Sem: SSSem P P' St Tr):
  P'.(expr) -> St.(state) -> (nat -> Tr.(trace)) -> Prop :=
| omega_step_constr: forall es ss trs,
    (forall n, Sem.(step) (es n) (ss n) (trs n) (es (S n)) (ss (S n))) ->
    Sem.(omega_step) (es O) (ss O) trs.

Record DSem_SSSem_refine {P P' D S Tr} (Sem1: DSem P D) (Sem2: SSSem P P' S Tr)
  (R1: D.(domain) -> (S.(state) -> list Tr.(trace) -> P'.(expr) -> S.(state) -> Prop) -> Prop)
  (R2: D.(domain) -> (S.(state) -> (nat -> Tr.(trace)) -> Prop) -> Prop):
  Prop :=
{
  refine_terminate: forall e,
    R1 (Sem1.(denote) e) (fun s1 trs e2 s2 => Sem2.(multi_step) (Sem2.(interp) e) s1 trs e2 s2 /\ Sem2.(halt) e2 s2);
  refine_diverge: forall e,
    R2 (Sem1.(denote) e) (fun s trs => Sem2.(omega_step) (Sem2.(interp) e) s trs);
}.

