Require Import Coq.Lists.List.
Require Import VCF.TraceGeneral.

Record FDvgTrace (A: Type) (B: Type) :=
{
  head_events: list A;
  tail_event: B;
}.

Inductive DvgTrace (A: Type) (B: Type): Type :=
| Finite_Diverge (tr: FDvgTrace A B)
| Infinite_Diverge (tr: nat -> A).

Arguments head_events {A} {B} (_).
Arguments tail_event {A} {B} (_).
Arguments Finite_Diverge {A} {B} (_).
Arguments Infinite_Diverge {A} {B} (_).

Definition fd_trace_app {A B} (l1: list A) (l2: FDvgTrace A B): FDvgTrace A B :=
{|
  head_events := app l1 (head_events l2);
  tail_event := tail_event l2;
|}.

Definition diverge_trace_app {A B} (l1: list A) (l2: DvgTrace A B): DvgTrace A B :=
  match l2 with
  | Finite_Diverge l2' => Finite_Diverge (fd_trace_app l1 l2')
  | Infinite_Diverge l2' => Infinite_Diverge (natfunc_app l1 l2')
  end.

Lemma app_fd_trace_app: forall {A B} (l1 l2: list A) (l3: FDvgTrace A B),
  fd_trace_app l1 (fd_trace_app l2 l3) = fd_trace_app (l1 ++ l2) l3.
Proof.
  intros.
  unfold fd_trace_app; simpl.
  f_equal; apply app_assoc.
Qed.

Lemma app_diverge_trace_app: forall {A B} (l1 l2: list A) (l3: DvgTrace A B),
  diverge_trace_app l1 (diverge_trace_app l2 l3) = diverge_trace_app (l1 ++ l2) l3.
Proof.
  intros.
  destruct l3 as [l3' | l3'].
  + simpl.
    f_equal.
    apply app_fd_trace_app.
  + simpl.
    f_equal.
    apply app_natfunc_app.
Qed.

Lemma fd_trace_app_nil_l: forall {A B} (l: FDvgTrace A B),
  fd_trace_app nil l = l.
Proof. intros. destruct l; reflexivity. Qed.

Lemma diverge_trace_app_nil_l: forall {A B} (l: DvgTrace A B),
  diverge_trace_app nil l = l.
Proof.
  intros.
  destruct l as [l' | l'].
  + simpl.
    f_equal.
    apply fd_trace_app_nil_l.
  + simpl.
    reflexivity.
Qed.

Instance FDvgTrace_InfTrace (A B: Type): Trace.InfTrace (list A) (FDvgTrace A B) :=
{|
  Trace.inf_concat := fd_trace_app;
  Trace.fin_concat_inf_concat_assoc := app_fd_trace_app;
  Trace.empty_inf_concat := fd_trace_app_nil_l;
|}.

Instance DvgTrace_InfTrace (A B: Type): Trace.InfTrace (list A) (DvgTrace A B) :=
{|
  Trace.inf_concat := diverge_trace_app;
  Trace.fin_concat_inf_concat_assoc := app_diverge_trace_app;
  Trace.empty_inf_concat := diverge_trace_app_nil_l;
|}.

