(*************************************************)
(** Proof of the Bourbaki-Witt Fixpoint Theorem **)
(*************************************************)

(** This file is based on a course project of Shanghai Jiao Tong University,
    CS263 2020 spring, developed by Xinyi Wan and Zimeng Huang. Qinxiang Cao
    editted this file and add more theorems to it later. *)

Require Import ClassicalFacts.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationPairs.
Require Import VCF.LiftConstructors.
Require Import VCF.PairConstructors.

(* 基本定义*)
(**************************************)

Class AntiSymmetric_Setoid {A:Type} (R: A-> A-> Prop) (R':A->A->Prop): Prop :=
  antisymmetricity_setoid: forall a b, R a b -> R b a -> R' a b. 
(*反对称性*)

Class PartialOrder_Setoid {A:Type} (R: A-> A-> Prop)(R':A->A->Prop): Prop :=
{
  PO_AntiSymmetric_Setoid: AntiSymmetric_Setoid R R';
  PO_Reflexive_Setoid: forall x y, R' x y -> R x y;
  PO_Transitive: Transitive R
}.
(*偏序关系*)

Existing Instances PO_AntiSymmetric_Setoid PO_Transitive.

Instance PartialOrder_Setoid_Reflexive:forall A:Type, forall R R':A->A->Prop,
  Equivalence R' -> PartialOrder_Setoid R R' -> Reflexive R.
Proof.
  intros.
  hnf; intros.
  apply PO_Reflexive_Setoid.
  reflexivity.
Qed.

Instance PartialOrder_Setoid_Proper {A:Type} (R R': A -> A -> Prop) {equ: Equivalence R'} {PO: PartialOrder_Setoid R R'}: Proper (R' ==> R' ==> iff) R.
Proof.
  unfold Proper, respectful.
  intros.
  split; intros.
  + transitivity x0; [| apply PO_Reflexive_Setoid; auto].
    transitivity x; [apply PO_Reflexive_Setoid; symmetry; auto |].
    auto.
  + transitivity y0; [| apply PO_Reflexive_Setoid; symmetry; auto].
    transitivity y; [apply PO_Reflexive_Setoid; auto |].
    auto.
Qed.

Definition seq_upper_bound {A:Type} (R:A->A->Prop) (T: nat -> A) (bnd:A):Prop :=
forall n, R (T n) bnd.
(*检查bnd是否是一个无穷序列的上界*)

Definition seq_least_upper_bound {A:Type} (R:A->A->Prop) (T: nat -> A) (bnd:A): Prop :=
  seq_upper_bound R T bnd /\
  forall bnd', seq_upper_bound R T bnd' -> R bnd bnd'.
(*一个无穷序列的上确界*)

Definition least_element {A:Type} (bot:A) (R:A->A->Prop): Prop:=
forall a, R bot a.
(* 集合的最小元 *)

Definition seq_mono {A:Type} (R:A->A->Prop) (T: nat -> A): Prop :=
  forall n, R (T n) (T (S n)).

Class CompletePartialOrder_Setoid {A:Type} (R:A->A->Prop) (R': A-> A-> Prop) (limit: (nat -> A) -> A) (bot: A): Prop :=
{
  CPO_PartialOrder: PartialOrder_Setoid R R';
  CPO_SeqCont: forall T, seq_mono R T -> seq_least_upper_bound R T (limit T);
  limit_congr: forall T1 T2, (forall n, R' (T1 n) (T2 n)) -> R' (limit T1) (limit T2);
  CPO_least: least_element bot R;
}.

Existing Instance CPO_PartialOrder.

Definition seq_continuous {A:Type} (R R':A->A->Prop) (limit: (nat -> A) -> A) (f:A->A): Prop :=
  forall T,
    seq_mono R T ->
    R' (f (limit T)) (limit (Basics.compose f T)).
(* 函数连续性 *)

Definition fixpoint {A:Type} (f:A->A) (a:A)(R':A->A->Prop): Prop:=
R' a (f a).
(* 函数f的不动点, R' 为等价关系*)

Definition least_fixpoint {A:Type} (f:A->A) (R:A->A->Prop) (R':A->A->Prop)(a:A): Prop:=
fixpoint f a R' /\ forall a', fixpoint f a' R'-> R a a'.
(* 最小不动点 *)

Fixpoint F_iterate {A:Type}(F:A->A)(x:A)(n:nat):A:=
match n with
|O => x
|S n => F(F_iterate F x n)
end.
(* f(f(f...f(x)))的定义, 为方便描述, 记为f_n(x)*)

Definition BW_fix {A: Type} {R R': A -> A -> Prop} {limit bot} {CPO: CompletePartialOrder_Setoid R R' limit bot} (f: A -> A): A :=
  limit (F_iterate f bot).

(* 基本定义结束*)
(**************************************) 



(* 基本引理与证明指令 *)
(**************************************)

Lemma limit_smaller_iff: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {CPO: CompletePartialOrder_Setoid R R' limit bot} xs y,
  seq_mono R xs ->
  (R (limit xs) y <-> (forall n, R (xs n) y)).
Proof.
  intros.
  split; intros.
  + rewrite <- H0.
    destruct (CPO_SeqCont xs); auto.
  + destruct (CPO_SeqCont xs); auto.
Qed.

Lemma limit_greater: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {CPO: CompletePartialOrder_Setoid R R' limit bot} xs y,
  seq_mono R xs ->
  (exists n, R y (xs n)) ->
  R y (limit xs).
Proof.
  intros.
  destruct H0 as [n ?].
  rewrite H0.
  destruct (CPO_SeqCont xs); auto.
Qed.

Theorem limit_mono: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {equ: Equivalence R'} {CPO: CompletePartialOrder_Setoid R R' limit bot},
  forall T1 T2,
    seq_mono R T1 ->
    seq_mono R T2 ->
    lift_rel2 R T1 T2 ->
    R (limit T1) (limit T2).
Proof.
  intros.
  apply limit_smaller_iff; auto.
  intros.
  apply limit_greater; auto.
  exists n; auto.
Qed.

(*Module OrderTac.*)

Ltac solve_order R (*test_bot test_limit test_Proper1 test_Proper2*) :=
  match goal with
  | H: R ?x ?y |- R ?x ?y =>
      exact H
  | |- R ?x ?x =>
      reflexivity
  | CPO: CompletePartialOrder_Setoid R ?R' ?limit ?bot |- R ?bot _ =>
      apply CPO_least
  | CPO: CompletePartialOrder_Setoid R ?R' ?limit ?bot |- R (?limit ?xs) (?limit ?ys) =>
      solve [ apply limit_mono;
                [ solve_seq_mono R
                | solve_seq_mono R
                | unfold lift_rel2;
                  let n := fresh "n" in
                  intros n;
                  solve_order_ind R n
                ]
            ]
  | CPO: CompletePartialOrder_Setoid R ?R' ?limit ?bot |- R (?limit ?xs) ?y =>
      let H := fresh "H" in
      assert (seq_mono R xs) as H;
      [ solve_seq_mono R
      | apply (proj2 (@limit_smaller_iff _ _ _ _ _ CPO xs y H));
        let n := fresh "n" in
        intros n;
        clear H;
        solve_order_ind R n
      ]
  | CPO: CompletePartialOrder_Setoid R ?R' ?limit ?bot, H: ?R' ?x ?y |- R ?x ?y =>
      apply PO_Reflexive_Setoid, H
  | CPO: CompletePartialOrder_Setoid R ?R' ?limit ?bot, H: ?R' ?y ?x |- R ?x ?y =>
      apply PO_Reflexive_Setoid; symmetry; apply H
  | HP1: Proper (?RB ==> R) ?f |- R (?f _) (?f _) =>
      apply HP1; solve_order RB
  | HP2: Proper (?RB1 ==> ?RB2 ==> R) ?f |- R (?f _ _) (?f _ _) =>
      apply HP2; [solve_order RB1 | solve_order RB2]
  | HP3: Proper (?RB1 ==> ?RB2 ==> ?RB3 ==> R) ?f |- R (?f _ _ _) (?f _ _ _) =>
      apply HP3; [solve_order RB1 | solve_order RB2 | solve_order RB3]
  | Hsm: seq_mono R ?xs |- R (?xs ?n) (?xs (S ?n)) =>
      exact (Hsm n)
  | Hsb: seq_upper_bound R ?xs ?y |- R (?xs ?n) ?y =>
      exact (Hsb n)
  | |- _ => auto
  end
with solve_order_ind R n :=
  first
    [ progress (solve_order R)
    | solve
        [ let IH := fresh "IH" n in
          induction n as [| n IH]; [simpl | simpl in IH |- *]; solve_order R
        ]
    | idtac
    ]
with solve_seq_mono R :=
  match goal with
  | |- seq_mono R ?xs =>
      let n := fresh "n" in
      intros n;
      solve_order_ind R n
  | |- _ => idtac
  end
with solve_seq_upper_bound R :=
  match goal with
  | |- seq_upper_bound R ?xs ?y =>
      let n := fresh "n" in
      intros n;
      solve_order_ind R n
  | |- _ => idtac
  end.

(* 一些性质与引理的证明*)
(**************************************)

Lemma const_limit: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {equ: Equivalence R'} {CPO: CompletePartialOrder_Setoid R R' limit bot} c,
  R' (limit (fun n => c)) c.
Proof.
  intros.
  apply antisymmetricity_setoid.
  + solve_order R.
  + apply limit_greater; [solve_seq_mono R |].
    exists 0; reflexivity.
Qed.

Lemma seq_mono_nat_le: forall {A R} {rfR: Reflexive R} {trR: Transitive R} (T: nat -> A),
  seq_mono R T ->
  forall n m, n <= m -> R (T n) (T m).
Proof.
  intros.
  induction H0.
  + reflexivity.
  + etransitivity; eauto.
Qed.

Lemma seq_least_upper_bound_unique: forall {A: Type} {R R': A -> A -> Prop}
  {CPO: PartialOrder_Setoid R R'},
  forall T bnd1 bnd2,
  seq_least_upper_bound R T bnd1 ->
  seq_least_upper_bound R T bnd2 ->
  R' bnd1 bnd2.
Proof.
  intros.
  destruct H, H0.
  apply H2 in H.
  apply H1 in H0.
  apply antisymmetricity_setoid; auto.
Qed.

Lemma F_iterate_bot_mono: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {CPO: CompletePartialOrder_Setoid R R' limit bot},
  forall f,
    Proper (R ==> R) f ->
    seq_mono R (F_iterate f bot).
Proof. intros. solve_seq_mono R. Qed.

Lemma seq_mono_without_0_seq_mono: forall (A: Type) (R: A -> A -> Prop) T,
  seq_mono R T ->
  seq_mono R (fun n => T (S n)).
Proof. intros. solve_seq_mono R. Qed.

Lemma seq_mono_without_0_upper_bound: forall (A: Type) (R: A -> A -> Prop) T bnd,
  seq_mono R T ->
  seq_upper_bound R T bnd ->
  seq_upper_bound R (fun n => T (S n)) bnd.
Proof. intros. solve_seq_upper_bound R. Qed.

Lemma seq_mono_without_0_upper_bound_inv: forall (A: Type) (R: A -> A -> Prop),
  Transitive R ->
  forall T bnd,
  seq_mono R T ->
  seq_upper_bound R (fun n => T (S n)) bnd ->
  seq_upper_bound R T bnd.
Proof.
  unfold seq_upper_bound.
  intros.
  destruct n; [| apply H1; auto].
  transitivity (T (S O)); [apply H0 | apply H1].
Qed.

Lemma seq_mono_without_0_least_upper_bound: forall (A: Type) (R: A -> A -> Prop),
  Transitive R ->
  forall T bnd,
  seq_mono R T ->
  seq_least_upper_bound R T bnd ->
  seq_least_upper_bound R (fun n => T (S n)) bnd.
Proof.
  unfold seq_least_upper_bound; intros.
  destruct H1.
  split; intros.
  + apply seq_mono_without_0_upper_bound; auto.
  + apply seq_mono_without_0_upper_bound_inv in H3; auto.
Qed.

Lemma seq_mono_without_0_limit: forall {A: Type} {R R': A -> A -> Prop} {limit bot}
  {CPO: CompletePartialOrder_Setoid R R' limit bot},
  forall T,
  seq_mono R T ->
  R' (limit T) (limit (fun n => T (S n))).
Proof.
  intros.
  pose proof CPO_SeqCont T H.
  pose proof CPO_SeqCont _ ltac:(eapply seq_mono_without_0_seq_mono; eauto).
  apply seq_mono_without_0_least_upper_bound in H0; auto; [| apply CPO].
  eapply seq_least_upper_bound_unique; eauto.
Qed.

Theorem seq_mono_squeeze_limit: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {equ: Equivalence R'} {CPO: CompletePartialOrder_Setoid R R' limit bot},
  forall T1 T2,
    seq_mono R T1 ->
    seq_mono R T2 ->
    (forall n, R (T1 n) (T2 n)) ->
    (forall n, R (T2 n) (limit T1)) ->
    R' (limit T1) (limit T2).
Proof.
  intros.
  eapply seq_least_upper_bound_unique; [| apply CPO_SeqCont; auto].
  split.
  + intros; auto.
  + intros.
    solve_order R.
    etransitivity; [apply H1 | apply H3].
Qed.

(* 引理证明结束*)

(**************************************) 

(* 定理:<当A,R>是完备偏序集, 函数f单调且连续, 集合存在最小元时, (F_iterate_set f bot)的上确界是函数f的不动点 *)

Theorem BourbakiWitt_fixpoint: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {equ: Equivalence R'} {CPO: CompletePartialOrder_Setoid R R' limit bot},
  forall f,
    Proper (R ==> R) f ->
    seq_continuous R R' limit f ->
    R' (BW_fix f) (f (BW_fix f)).
Proof.
  intros.
  unfold BW_fix.
  rewrite H0 by (solve_seq_mono R).
  rewrite seq_mono_without_0_limit by (solve_seq_mono R).
  apply limit_congr.
  intros; reflexivity.
Qed.

Theorem BourbakiWitt_least_fixpoint: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {equ: Equivalence R'} {CPO: CompletePartialOrder_Setoid R R' limit bot},
  forall f p,
    Proper (R ==> R) f ->
    seq_continuous R R' limit f ->
    fixpoint f p R' ->
    R (BW_fix f) p.
Proof.
  intros.
  unfold BW_fix.
  set (L := F_iterate f bot).
  pose proof CPO_SeqCont L.
  assert (seq_mono R L) by (eapply F_iterate_bot_mono; eauto).
  specialize (H2 H3) as [? ?].
  apply H4.
  hnf; intros.
  unfold fixpoint in H1.
  clear - CPO equ H H1; subst L.
  induction n; simpl.
  + apply CPO_least.
  + rewrite H1.
    apply H; auto.
Qed.

(*更宽松的定理，不一定用F本身迭代，而可以用更大的步伐迭代*)

Theorem BourbakiWitt_fixpoint_relax: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {equ: Equivalence R'} {CPO: CompletePartialOrder_Setoid R R' limit bot},
  forall f g,
    Proper (R ==> R) f ->
    Proper (R ==> R) g ->
    seq_continuous R R' limit f ->
    seq_continuous R R' limit g ->
    (forall a b, R a b -> R a (f a) -> R (f a) (g b)) ->
    (forall b, (forall a, R a b -> R (f a) b) -> (forall a, R a b -> R (g a) b)) ->
    R' (BW_fix f) (BW_fix g).
Proof.
  intros.
  assert (forall n, R (F_iterate f bot n) (F_iterate g bot n)).
  {
    intros.
    induction n.
    + simpl; reflexivity.
    + pose proof F_iterate_bot_mono  _ H n.
      simpl.
      apply H3; auto.
  }
  assert (forall n, R (F_iterate g bot n) (BW_fix f)).
  {
    intros.
    induction n.
    + apply CPO_least.
    + simpl.
      apply H4; auto.
      intros.
      rewrite BourbakiWitt_fixpoint by auto.
      apply H; auto.
  }
  unfold BW_fix.
  apply seq_mono_squeeze_limit; auto;
  apply F_iterate_bot_mono; auto.
Qed.

(*如果两个函数一个比另一个大，则他们的不动点也有对应大小关系*)

Theorem BourbakiWitt_fixpoint_monotonic: forall {A: Type} {R R': A -> A -> Prop} {limit bot} {equ: Equivalence R'} {CPO: CompletePartialOrder_Setoid R R' limit bot},
  forall f g,
    Proper (R ==> R) f ->
    Proper (R ==> R) g ->
    seq_continuous R R' limit f ->
    seq_continuous R R' limit g ->
    (forall a b, R a b -> R (f a) (g b)) ->
    R (BW_fix f) (BW_fix g).
Proof.
  intros.
  unfold BW_fix.
  solve_order R.
Qed.

(**************************************)

(** CPO的实例与构造 *)

Lemma Prop_exists_False_CPO: CompletePartialOrder_Setoid (fun P Q: Prop => P -> Q) iff (@ex _) False.
Proof.
  constructor.
  + constructor.
    - hnf; tauto.
    - intros; tauto.
    - hnf; intros; tauto.
  + intros.
    split.
    - hnf; intros.
      exists n; auto.
    - intros.
      destruct H1 as [n ?].
      apply H0 in H1.
      auto.
  + intros; firstorder.
  + hnf; intros.
    tauto.
Qed.

Lemma Prop_forall_True_CPO: CompletePartialOrder_Setoid (fun P Q: Prop => Q -> P) iff (fun P => forall n, P n) True.
Proof.
  constructor.
  + constructor.
    - hnf; tauto.
    - intros; tauto.
    - hnf; intros; tauto.
  + intros.
    split.
    - hnf; intros.
      apply H; auto.
    - intros.
      apply H0; auto.
  + intros; firstorder.
  + hnf; intros.
    tauto.
Qed.

Lemma lift_CPO
        (A: Type)
        {B: Type}
        {RB RB': B -> B -> Prop}
        {limitB botB}
        (CPOB: CompletePartialOrder_Setoid RB RB' limitB botB):
  @CompletePartialOrder_Setoid
    (A -> B)
    (lift_rel2 RB)
    (lift_rel2 RB')
    (lift_binder limitB)
    (lift_fun0 botB)
.
Proof.
  unfold lift_rel2, lift_binder, lift_fun0.
  constructor.
  + constructor.
    - hnf; intros.
      apply PO_AntiSymmetric_Setoid; auto.
    - intros.
      apply PO_Reflexive_Setoid; auto.
    - hnf; intros.
      eapply PO_Transitive; auto.
  + intros.
    pose proof fun a => CPO_SeqCont (fun n => T n a).
    split.
    - hnf; intros.
      specialize (H0 a ltac:(intro; apply H)).
      destruct H0.
      apply H0.
    - intros.
      specialize (H0 a ltac:(intro; apply H)).
      destruct H0.
      apply H2.
      hnf; intros; apply H1.
  + intros.
    apply limit_congr.
    intros; apply H.
  + hnf; intros.
    apply CPO_least.
Qed.

Lemma pair_CPO
        {A B AB: Type}
        (projA: AB -> A)
        (projB: AB -> B)
        {RA RA': A -> A -> Prop}
        {RB RB': B -> B -> Prop}
        (RAB RAB': AB -> AB -> Prop)
        {limitA botA limitB botB} limitAB botAB
        (CPOA: CompletePartialOrder_Setoid RA RA' limitA botA)
        (CPOB: CompletePartialOrder_Setoid RB RB' limitB botB):
  (forall c1 c2, RAB c1 c2 <-> RA (projA c1) (projA c2) /\ RB (projB c1) (projB c2)) ->
  (forall c1 c2, RAB' c1 c2 <-> RA' (projA c1) (projA c2) /\ RB' (projB c1) (projB c2)) ->
  (forall cs, projA (limitAB cs) = limitA (fun n => projA (cs n)) /\ projB (limitAB cs) = limitB (fun n => projB (cs n))) ->
  (projA botAB = botA /\ projB botAB = botB) ->
  (forall c1 c2, projA c1 = projA c2 -> projB c1 = projB c2 -> c1 = c2) ->
  @CompletePartialOrder_Setoid AB RAB RAB' limitAB botAB.
Proof.
  intros HR HR' Hlimit Hbot Hproj.
  constructor.
  + constructor.
    - hnf; intros.
      rewrite HR in H, H0; rewrite HR'.
      destruct H, H0.
      split; apply antisymmetricity_setoid; auto.
    - intros.
      rewrite HR' in H; rewrite HR.
      destruct H.
      split; apply PO_Reflexive_Setoid; auto.
    - hnf; intros.
      rewrite HR in H, H0 |- *.
      destruct H, H0.
      split; etransitivity; eauto.
  + intros.
    assert (seq_mono RA (fun n => projA (T n))).
    {
      hnf; intros.
      specialize (H n).
      rewrite HR in H.
      destruct H; auto.
    }
    assert (seq_mono RB (fun n => projB (T n))).
    {
      hnf; intros.
      specialize (H n).
      rewrite HR in H.
      destruct H; auto.
    }
    apply CPO_SeqCont in H0.
    apply CPO_SeqCont in H1.
    destruct H0, H1.
    destruct (Hlimit T) as [HHA HHB].
    split.
    - hnf; intros.
      rewrite HR.
      rewrite HHA, HHB.
      split; [apply H0 | apply H1].
    - intros.
      rewrite HR.
      rewrite HHA, HHB.
      split; [apply H2 | apply H3]; auto.
      * intros n; specialize (H4 n); simpl in H4; rewrite HR in H4; tauto.
      * intros n; specialize (H4 n); simpl in H4; rewrite HR in H4; tauto.
  + intros.
    rewrite HR'.
    destruct (Hlimit T1) as [HHA1 HHB1].
    destruct (Hlimit T2) as [HHA2 HHB2].
    rewrite HHA1, HHB1, HHA2, HHB2.
    split; apply limit_congr; intros n; specialize (H n); rewrite HR' in H; tauto.
  + hnf.
    intros.
    rewrite HR.
    rewrite (proj1 Hbot), (proj2 Hbot).
    split; apply CPO_least.
Qed.

Lemma prod_pair_CPO
        {A B: Type}
        {RA RA': A -> A -> Prop}
        {RB RB': B -> B -> Prop}
        {limitA botA limitB botB}
        {CPOA: CompletePartialOrder_Setoid RA RA' limitA botA}
        {CPOB: CompletePartialOrder_Setoid RB RB' limitB botB}:
  @CompletePartialOrder_Setoid
    (A * B)
    (pair_rel2 RA RB)
    (pair_rel2 RA' RB')
    (pair_binder limitA limitB)
    (pair_fun0 botA botB).
Proof.
  intros.
  eapply (pair_CPO fst snd); [ typeclasses eauto |  typeclasses eauto | ..].
  + intros; reflexivity.
  + intros; reflexivity.
  + intros; split; reflexivity.
  + intros; split; reflexivity.
  + intros [? ?] [? ?]; simpl; intros; subst; reflexivity.
Qed.


(* 复杂CPO导出 *)
(**************************************)

Class CPO_Domain (A: Type): Type := {
  CPO_R: A -> A -> Prop;
  CPO_R': A -> A -> Prop;
  CPO_limit: (nat -> A) -> A;
  CPO_bot: A;
  CPO_Equiv: Equivalence CPO_R';
  CPO_CPO: CompletePartialOrder_Setoid CPO_R CPO_R' CPO_limit CPO_bot;
}.

Existing Instances CPO_Equiv CPO_CPO.

Instance Lift_CPO_Domain {A B: Type} {CPO_B: CPO_Domain B}: CPO_Domain (A -> B) :=
  Build_CPO_Domain
    (A -> B)
    (lift_rel2 CPO_R)
    (lift_rel2 CPO_R')
    (lift_binder CPO_limit)
    (lift_fun0 CPO_bot)
    ltac:(apply pointwise_equivalence; typeclasses eauto)
    ltac:(apply lift_CPO; typeclasses eauto).
  
Instance Pair_CPO_Domain {A B: Type} {CPO_A: CPO_Domain A} {CPO_B: CPO_Domain B}: CPO_Domain (A * B) :=
  Build_CPO_Domain
    (A * B)
    (pair_rel2 CPO_R CPO_R)
    (pair_rel2 CPO_R' CPO_R')
    (pair_binder CPO_limit CPO_limit)
    (pair_fun0 CPO_bot CPO_bot)
    ltac:(refine (RelProd_Equivalence _ _ _ _); typeclasses eauto)
    ltac:(apply prod_pair_CPO).

(* 二维逼近Fixpoint *)

Definition BW_fix2
             {A B}
             {RA RA': A -> A -> Prop}
             {RB RB': B -> B -> Prop}
             {limitA botA limitB botB}
             {CPOA: CompletePartialOrder_Setoid RA RA' limitA botA}
             {CPOB: CompletePartialOrder_Setoid RB RB' limitB botB}
             (f: A -> B -> A) (g: A -> B -> B): A * B :=
  @BW_fix
    (A * B)
    (RelProd RA RB)
    (RelProd RA' RB')
    (fun cs => (limitA (fun n => fst (cs n)), limitB (fun n => snd (cs n))))
    (botA, botB)
    (pair_CPO
       (@fst A B)
       (@snd A B)
      (RelProd RA RB)
      (RelProd RA' RB')
       (fun cs => (limitA (fun n => fst (cs n)), limitB (fun n => snd (cs n))))
       (botA, botB)
       CPOA
       CPOB
       ltac:(intros; reflexivity)
       ltac:(intros; reflexivity)
       ltac:(intros; split; reflexivity)
       ltac:(split; reflexivity)
       ltac:(intros [? ?] [? ?]; simpl; intros; congruence))
       (fun c => (f (fst c) (snd c), g (fst c) (snd c))).

(* 二维逼近的同一性 *)

Corollary two_dimensional_fix_coincide:
  forall {A B: Type}
         {RA RA': A -> A -> Prop}
         {RB RB': B -> B -> Prop}
         {limitA botA limitB botB}
         {equA: Equivalence RA'}
         {equB: Equivalence RB'}
         {CPOA: CompletePartialOrder_Setoid RA RA' limitA botA}
         {CPOB: CompletePartialOrder_Setoid RB RB' limitB botB},
  forall (f: A -> B -> A) (g: A -> B -> B)
    (Hf_ProperR: Proper (RA ==> RB ==> RA) f)
    (Hg_ProperR: Proper (RA ==> RB ==> RB) g)
    (Hf_Cont: forall a b, RA' (f (limitA a) (limitB b)) (limitA (fun n => f (a n) (b n))))
    (Hg_Cont: forall a b, RB' (g (limitA a) (limitB b)) (limitB (fun n => g (a n) (b n)))),
    (RelProd RA' RB')
      (BW_fix2 f g)
      (BW_fix2 (fun _ b => BW_fix (fun a => f a b)) (fun a _ => BW_fix (fun b => g a b))).
Proof.
  intros.
  assert (Proper (RA' ==> RB' ==> RA') f) as Hf_ProperR'.
  {
    hnf; intros; hnf; intros.
    apply antisymmetricity_setoid.
    + solve_order RA.
    + solve_order RA.
  }
  assert (Proper (RA' ==> RB' ==> RB') g) as Hg_ProperR'.
  {
    hnf; intros; hnf; intros.
    apply antisymmetricity_setoid.
    + solve_order RB.
    + solve_order RB.
  }
  assert (forall n,
             RA (fst (F_iterate
                        (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) n))
                (fst (F_iterate
                        (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) (S n))) /\
             RB (snd (F_iterate
                        (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) n))
                (snd (F_iterate
                        (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) (S n)))).
  {
    induction n; simpl.
    + split; apply CPO_least.
    + split; [apply Hf_ProperR | apply Hg_ProperR]; tauto.
  }
  assert (seq_mono RA
            (fun n =>
               fst (F_iterate
                      (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) n)))
      as Hf_seq_mono1.
  {
    hnf; intros n; apply (H n).
  }
  assert (seq_mono RB
            (fun n =>
               snd (F_iterate
                      (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) n)))
      as Hg_seq_mono1.
  {
    hnf; intros n; apply (H n).
  }
  clear H.
  assert (forall b, Proper (RA ==> RA) (fun a => f a b)) as Hf_mono.
  {
    intros; hnf; intros.
    apply Hf_ProperR; auto.
    reflexivity.
  }
  assert (forall a, Proper (RB ==> RB) (fun b => g a b)) as Hg_mono.
  {
    intros; hnf; intros.
    apply Hg_ProperR; auto.
    reflexivity.
  }
  assert (forall n,
            RA
              (fst (F_iterate (fun c =>
                (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b))) (botA, botB) n))
              (fst (F_iterate (fun c =>
                (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b))) (botA, botB) (S n))) /\
            RB
              (snd (F_iterate (fun c =>
                (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b))) (botA, botB) n))
              (snd (F_iterate (fun c =>
                (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b))) (botA, botB) (S n)))).
  {
    induction n.
    + simpl.
      split; apply CPO_least.
    + simpl; split.
      - apply BourbakiWitt_fixpoint_monotonic; auto.
        * hnf; intros.
          match goal with
          | |- RA' (f _ ?c) _ => rewrite <- (const_limit c) at 1
          end.
          apply Hf_Cont.
        * hnf; intros.
          match goal with
          | |- RA' (f _ ?c) _ => rewrite <- (const_limit c) at 1
          end.
          apply Hf_Cont.
        * intros.
          apply Hf_ProperR; auto.
          apply (proj2 IHn).
      - apply BourbakiWitt_fixpoint_monotonic; auto.
        * hnf; intros.
          match goal with
          | |- RB' (g ?c _) _ => rewrite <- (const_limit c) at 1
          end.
          apply Hg_Cont.
        * hnf; intros.
          match goal with
          | |- RB' (g ?c _) _ => rewrite <- (const_limit c) at 1
          end.
          apply Hg_Cont.
        * intros.
          apply Hg_ProperR; auto.
          apply (proj1 IHn).
  }
  assert (seq_mono RA
            (fun n =>
               fst (F_iterate (fun c =>
                      (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b))) (botA, botB) n)))
      as Hf_seq_mono2.
  {
    hnf; intros n; apply (H n).
  }
  assert (seq_mono RB
            (fun n =>
               snd (F_iterate (fun c =>
                      (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b))) (botA, botB) n)))
      as Hg_seq_mono2.
  {
    hnf; intros n; apply (H n).
  }
  clear H.

  assert (forall n,
    RA
      (fst (F_iterate (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) n))
      (fst (F_iterate
              (fun c => (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b)))
              (botA, botB) n)) /\
    RB
      (snd (F_iterate (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) n))
      (snd (F_iterate
              (fun c => (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b)))
              (botA, botB) n))) as HR12.
  {
    induction n; simpl.
    + split; reflexivity.
    + destruct IHn as [IHn_f IHn_g].
      split.
      - match goal with
        | |- RA _ (BW_fix ?f) =>
               rewrite <- (proj1 (CPO_SeqCont (F_iterate f botA) (F_iterate_bot_mono f ltac:(auto))) (S n))
        end.
        match goal with
        | |- RA (f _ _) (F_iterate (fun a => f a ?_b0) _ _) =>
               set (b0 := _b0) in IHn_g |- *;
               clearbody b0
        end.
        clear IHn_f.
        induction n; simpl.
        * apply Hf_ProperR; [reflexivity | auto].
        * apply Hf_ProperR; [| auto].
          simpl in IHn.
          apply IHn.
          rewrite <- IHn_g.
          apply Hg_seq_mono1.
      - match goal with
        | |- RB _ (BW_fix ?g) =>
               rewrite <- (proj1 (CPO_SeqCont (F_iterate g botB) (F_iterate_bot_mono g ltac:(auto))) (S n))
        end.
        match goal with
        | |- RB (g _ _) (F_iterate (fun b => g ?_a0 _) _ _) =>
               set (a0 := _a0) in IHn_f |- *;
               clearbody a0
        end.
        clear IHn_g.
        induction n; simpl.
        * apply Hg_ProperR; [auto | reflexivity].
        * apply Hg_ProperR; [auto |].
          simpl in IHn.
          apply IHn.
          rewrite <- IHn_f.
          apply Hf_seq_mono1.
  }

  let t := eval unfold BW_fix2 in (BW_fix2 f g) in
    match t with
    | @BW_fix ?A0 ?R0 ?R0' ?limit0 ?bot0 ?CPO0 ?F =>
        pose proof @BourbakiWitt_fixpoint A0 R0 R0' limit0 bot0 ltac:(apply RelProd_Equivalence; auto) CPO0 F
    end.
  assert (Proper ((RA * RB)%signature ==> (RA * RB)%signature) (fun c : A * B => (f (fst c) (snd c), g (fst c) (snd c)))).
  {
    hnf; intros [? ?] [? ?] [? ?].
    split; [apply Hf_ProperR | apply Hg_ProperR]; auto.
  }
  specialize (H H0); clear H0.
  assert (seq_continuous (RA * RB)%signature (RA' * RB')%signature
        (fun cs : nat -> A * B =>
         (limitA (fun n : nat => fst (cs n)), limitB (fun n : nat => snd (cs n))))
        (fun c : A * B => (f (fst c) (snd c), g (fst c) (snd c)))).
  {
    hnf; intros.
    constructor; [apply Hf_Cont | apply Hg_Cont].
  }
  specialize (H H0); clear H0.
  destruct H as [Hf_fix Hg_fix].
  unfold RelCompFun in Hf_fix, Hg_fix; simpl in Hf_fix, Hg_fix.

  assert (forall n,
    RA
      (fst
         (F_iterate
            (fun c => (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b))) 
            (botA, botB) n))
      (limitA
         (fun n => fst (F_iterate (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) n))) /\
    RB
      (snd
         (F_iterate
            (fun c => (BW_fix (fun a => f a (snd c)), BW_fix (fun b => g (fst c) b))) 
            (botA, botB) n))
      (limitB
         (fun n => snd (F_iterate (fun c => (f (fst c) (snd c), g (fst c) (snd c))) (botA, botB) n)))) as H2fix.
  {
    intros.
    induction n; simpl.
    + split; apply CPO_least.
    + destruct IHn as [IHn_f IHn_g].
      split.
      - match goal with
        | |- RA (BW_fix (fun a => f a ?_b)) _ => set (b0 := _b) in IHn_g |- *; clearbody b0
        end.
        clear n IHn_f.
        match goal with
        | |- RA (BW_fix ?f) _ => apply (proj2 (CPO_SeqCont (F_iterate f botA) (F_iterate_bot_mono f ltac:(auto))))
        end.
        hnf; intros.
        induction n; simpl; [apply CPO_least |].
        rewrite (Hf_ProperR _ _ IHn _ _ IHn_g).
        rewrite <- Hf_fix.
        reflexivity.
      - match goal with
        | |- RB (BW_fix (fun b => g ?_a b)) _ => set (a0 := _a) in IHn_f |- *; clearbody a0
        end.
        clear n IHn_g.
        match goal with
        | |- RB (BW_fix ?f) _ => apply (proj2 (CPO_SeqCont (F_iterate f botB) (F_iterate_bot_mono f ltac:(auto))))
        end.
        hnf; intros.
        induction n; simpl; [apply CPO_least |].
        rewrite (Hg_ProperR _ _ IHn_f _ _ IHn).
        rewrite <- Hg_fix.
        reflexivity.
  }

  constructor; unfold RelCompFun.
  + unfold BW_fix2, BW_fix at 1 2.
    simpl fst.
    apply seq_mono_squeeze_limit; auto.
    - intros n; apply (proj1 (HR12 n)).
    - intros n; apply (proj1 (H2fix n)).
  + unfold BW_fix2, BW_fix at 1 2.
    simpl snd.
    apply seq_mono_squeeze_limit; auto.
    - intros n; apply (proj2 (HR12 n)).
    - intros n; apply (proj2 (H2fix n)).
Qed.


