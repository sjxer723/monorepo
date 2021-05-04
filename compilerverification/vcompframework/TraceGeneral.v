Require Import Coq.Lists.List.
Require Import VCF.SetsDomain.

Module Trace.

Class FinTrace (finT: Type): Type := {
  empty: finT;
  fin_concat: finT -> finT -> finT;
  fin_concat_assoc: forall tr1 tr2 tr3,
    fin_concat tr1 (fin_concat tr2 tr3) = fin_concat (fin_concat tr1 tr2) tr3;
  empty_fin_concat: forall tr,
    fin_concat empty tr = tr;
  fin_concat_empty: forall tr,
    fin_concat tr empty = tr;
}.

Class InfTrace (finT: Type) (infT: Type) {finTr: FinTrace finT}: Type := {
  inf_concat: finT -> infT -> infT;
  fin_concat_inf_concat_assoc: forall tr1 tr2 tr3,
    inf_concat tr1 (inf_concat tr2 tr3) = inf_concat (fin_concat tr1 tr2) tr3;
  empty_inf_concat: forall tr,
    inf_concat empty tr = tr;
}.

Class EventTrace (EV: Type) (T: Type): Type := {
  only_events: (EV -> Prop) -> T -> Prop;
}.

Record EventHandler {EV T} {ETr: EventTrace EV T} (A B: EV -> Prop) := {
  handler_rel: EV -> T -> Prop;
  handler_rel_event_wd: forall E tr, handler_rel E tr -> A E;
  handler_rel_trace_wd: forall E tr, handler_rel E tr -> only_events B tr;
}.

Class InterpTrace (EV: Type) (T: Type) {ETr: EventTrace EV T}: Type := {
  refines: forall {A B}, EventHandler A B -> T -> T -> Prop;
  refines_only_events: forall A B C (eh: EventHandler A B) tr tr',
    refines eh tr tr' ->
    only_events (Sets.union A C) tr ->
    only_events (Sets.union B C) tr'
}.

End Trace.

Instance list_FinTrace (A: Type): Trace.FinTrace (list A) :=
{|
  Trace.empty := nil;
  Trace.fin_concat := @app A;
  Trace.fin_concat_assoc := @app_assoc A;
  Trace.empty_fin_concat := @app_nil_l A;
  Trace.fin_concat_empty := @app_nil_r A;
|}.

Definition natfunc_app {A: Type} (l1: list A) (l2: nat -> A): nat -> A :=
  (fix app (l1: list A) (n: nat): A :=
    match l1 with
    | nil => l2 n
    | a :: l1' => match n with
                  | O => a
                  | S n' => app l1' n'
                  end
    end) l1.

Lemma app_natfunc_app: forall {A} (l1 l2: list A) (l3: nat -> A),
  natfunc_app l1 (natfunc_app l2 l3) = natfunc_app (l1 ++ l2) l3.
Proof.
  intros.
  induction l1.
  + simpl.
    unfold natfunc_app.
    reflexivity.
  + simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma natfunc_app_nil_l: forall {A} (l: nat -> A),
  natfunc_app nil l = l.
Proof.
  intros.
  reflexivity.
Qed.

Instance natfunc_FinTrace (A: Type): Trace.InfTrace (list A) (nat -> A) :=
{|
  Trace.inf_concat := @natfunc_app A;
  Trace.fin_concat_inf_concat_assoc := @app_natfunc_app A;
  Trace.empty_inf_concat := @natfunc_app_nil_l A;
|}.

(* TODO question, what about the composition between parallel composition and refines. *)
