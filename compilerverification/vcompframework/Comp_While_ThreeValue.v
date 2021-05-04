Require Import List.
Require Import Psatz.
Require Import Classical.
Require Import ZArith.
Require Import VCF.Sem.
Require Import VCF.ZFuncDomain.
Require Import VCF.SetsDomain.
Require Import VCF.BinRelDomain.
Require VCF.WhileLang.
Require VCF.WhileLang_RelSem.
Require VCF.ThreeValueWhileLang.

Import ListNotations.

Module S.
Include VCF.WhileLang.
Include VCF.WhileLang_RelSem.
End S.

Module T := VCF.ThreeValueWhileLang.

Fixpoint max_var_aexp (a: S.aexp): S.var :=
  match a with
  | S.APlus a1 a2 => Nat.max (max_var_aexp a1) (max_var_aexp a2)
  | S.AMinus a1 a2 => Nat.max (max_var_aexp a1) (max_var_aexp a2)
  | S.AMult a1 a2 => Nat.max (max_var_aexp a1) (max_var_aexp a2)
  | S.AId X => X
  | S.ANum _ => 0%nat
  end.

Fixpoint max_var_bexp (b: S.bexp): S.var :=
  match b with
  | S.BEq a1 a2 => Nat.max (max_var_aexp a1) (max_var_aexp a2)
  | S.BLe a1 a2 => Nat.max (max_var_aexp a1) (max_var_aexp a2)
  | S.BAnd b1 b2 => Nat.max (max_var_bexp b1) (max_var_bexp b2)
  | S.BNot b1 => max_var_bexp b1
  | S.BTrue => 0%nat
  | S.BFalse => 0%nat
  end.

Fixpoint max_var_com (c: S.com): S.var :=
  match c with
  | S.CAss X a => Nat.max X (max_var_aexp a)
  | S.CSkip => 0%nat
  | S.CSeq c1 c2 => Nat.max (max_var_com c1) (max_var_com c2)
  | S.CIf b c1 c2 => Nat.max (max_var_bexp b) (Nat.max (max_var_com c1) (max_var_com c2))
  | S.CWhile b c1 => Nat.max (max_var_bexp b) (max_var_com c1)
  end.

Fixpoint op_count_aexp (a: S.aexp): nat :=
  match a with
  | S.APlus a1 a2 => 1 + op_count_aexp a1 + op_count_aexp a2
  | S.AMinus a1 a2 => 1 + op_count_aexp a1 + op_count_aexp a2
  | S.AMult a1 a2 => 1 + op_count_aexp a1 + op_count_aexp a2
  | S.AId X => 0%nat
  | S.ANum _ => 1%nat
  end.

Fixpoint op_count_bexp (b: S.bexp): nat :=
  match b with
  | S.BEq a1 a2 => 1 + op_count_aexp a1 + op_count_aexp a2
  | S.BLe a1 a2 => 1 + op_count_aexp a1 + op_count_aexp a2
  | S.BAnd b1 b2 => 1 + op_count_bexp b1 + op_count_bexp b2
  | S.BNot b1 => 1 + op_count_bexp b1
  | S.BTrue => 1%nat
  | S.BFalse => 1%nat
  end.

Fixpoint op_count_com (c: S.com): S.var :=
  match c with
  | S.CAss X a => op_count_aexp a
  | S.CSkip => 0%nat
  | S.CSeq c1 c2 => op_count_com c1 + op_count_com c2
  | S.CIf b c1 c2 => op_count_bexp b + op_count_com c1 + op_count_com c2
  | S.CWhile b c1 => op_count_bexp b + op_count_com c1
  end.

Fixpoint translate_aexp (a: S.aexp) (bg: nat): list T.com * T.var :=
  match a with
  | S.APlus a1 a2 =>
      match translate_aexp a1 bg, translate_aexp a2 (bg + op_count_aexp a1) with
      | (c1, X1), (c2, X2) =>
           (c1 ++ c2 ++ [T.CAssBinop (bg + op_count_aexp a1 + op_count_aexp a2 + 1) T.APlus X1 X2],
            bg + op_count_aexp a1 + op_count_aexp a2 + 1)
      end
  | S.AMinus a1 a2 =>
      match translate_aexp a1 bg, translate_aexp a2 (bg + op_count_aexp a1) with
      | (c1, X1), (c2, X2) =>
           (c1 ++ c2 ++ [T.CAssBinop (bg + op_count_aexp a1 + op_count_aexp a2 + 1) T.AMinus X1 X2],
            bg + op_count_aexp a1 + op_count_aexp a2 + 1)
      end
  | S.AMult a1 a2 =>
      match translate_aexp a1 bg, translate_aexp a2 (bg + op_count_aexp a1) with
      | (c1, X1), (c2, X2) =>
           (c1 ++ c2 ++ [T.CAssBinop (bg + op_count_aexp a1 + op_count_aexp a2 + 1) T.AMult X1 X2],
            bg + op_count_aexp a1 + op_count_aexp a2 + 1)
      end
  | S.AId X => ([], X)
  | S.ANum n => ([T.CAssConst (bg + 1) n], bg + 1)
  end.

Fixpoint translate_bexp (b: S.bexp) (bg: nat): list T.com * T.var :=
  match b with
  | S.BEq a1 a2 =>
      match translate_aexp a1 bg, translate_aexp a2 (bg + op_count_aexp a1) with
      | (c1, X1), (c2, X2) =>
           (c1 ++ c2 ++ [T.CAssBinop (bg + op_count_aexp a1 + op_count_aexp a2 + 1) T.BEq X1 X2],
            bg + op_count_aexp a1 + op_count_aexp a2 + 1)
      end
  | S.BLe a1 a2 =>
      match translate_aexp a1 bg, translate_aexp a2 (bg + op_count_aexp a1) with
      | (c1, X1), (c2, X2) =>
           (c1 ++ c2 ++ [T.CAssBinop (bg + op_count_aexp a1 + op_count_aexp a2 + 1) T.BLe X1 X2],
            bg + op_count_aexp a1 + op_count_aexp a2 + 1)
      end
  | S.BAnd b1 b2 =>
      match translate_bexp b1 bg, translate_bexp b2 (bg + op_count_bexp b1) with
      | (c1, X1), (c2, X2) =>
           (c1 ++ c2 ++ [T.CAssBinop (bg + op_count_bexp b1 + op_count_bexp b2 + 1) T.BAnd X1 X2],
            bg + op_count_bexp b1 + op_count_bexp b2 + 1)
      end
  | S.BNot b1 =>
      match translate_bexp b1 bg with
      | (c1, X1) =>
           (c1 ++ [T.CAssUnop (bg + op_count_bexp b1 + 1) T.BNot X1],
            bg + op_count_bexp b1 + 1)
      end
  | S.BTrue => ([T.CAssConst (bg + 1) 1], bg + 1)
  | S.BFalse => ([T.CAssConst (bg + 1) 0], bg + 1)
  end.

Fixpoint translate_com (c: S.com) (bg: nat): T.com :=
  match c with
  | S.CSkip => T.CSkip
  | S.CAss X a =>
      match translate_aexp a bg with
      | (cs, Y) => fold_right T.CSeq (T.CAssVar X Y) cs
      end
  | S.CSeq c1 c2 =>
      T.CSeq (translate_com c1 bg) (translate_com c2 (bg + op_count_com c))
  | S.CIf b c1 c2 =>
      match translate_bexp b bg with
      | (cs, Y) => fold_right T.CSeq (T.CIf Y (translate_com c1 (bg + op_count_bexp b)) (translate_com c2 (bg + op_count_bexp b + op_count_com c1))) cs
      end
  | S.CWhile b c1 =>
      match translate_bexp b bg with
      | (cs, Y) => fold_right T.CSeq (T.CWhile Y (fold_left T.CSeq cs (translate_com c1 (bg + op_count_bexp b)))) cs
      end
  end.

Definition compile (c: S.com): T.com := translate_com c 0%nat.

Lemma translate_aexp_new_var_correct: forall a bg cs Y,
  translate_aexp a bg = (cs, Y) ->
  max_var_aexp a <= bg ->
  Y <= bg + op_count_aexp a.
Proof.
  induction a; intros; simpl in *.
  + injection H as ? ?; omega.
  + injection H as ? ?; omega.
  + destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H as ? ?; omega.
  + destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H as ? ?; omega.
  + destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H as ? ?; omega.
Qed.
  
Lemma translate_bexp_new_var_correct: forall b bg cs Y,
  translate_bexp b bg = (cs, Y) ->
  max_var_bexp b <= bg ->
  Y <= bg + op_count_bexp b.
Proof.
  induction b; intros; simpl in *.
  + injection H as ? ?; omega.
  + injection H as ? ?; omega.
  + destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H as ? ?; omega.
  + destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H as ? ?; omega.
  + destruct (translate_bexp b bg) as [cs1 Y1] eqn:?TR.
    injection H as ? ?; omega.
  + destruct (translate_bexp b1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_bexp b2 (bg + op_count_bexp b1)) as [cs2 Y2] eqn:?TR.
    injection H as ? ?; omega.
Qed.

Lemma translate_aexp_correct: forall a bg st1 st2 st3 cs Y,
  (forall X, X <= max_var_aexp a -> st1 X = st2 X) ->
  max_var_aexp a <= bg ->
  translate_aexp a bg = (cs, Y) ->
  T.ceval (fold_right T.CSeq T.CSkip cs) st2 st3 ->
  (forall X, X <= bg -> st2 X = st3 X) /\ S.aeval a st1 = st3 Y.
Proof.
  induction a; simpl max_var_aexp; intros.
  + simpl in H1.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite (Rel_concat_id _ _ _ _ _) in H2.
    destruct H2.
    split.
    - intros.
      apply H2; omega.
    - unfold S.aeval, S.constant_func.
      congruence.
  + simpl in H1.
    injection H1 as ? ?; subst.
    simpl in H2.
    unfold Rel.id in H2; subst.
    split; auto.
    simpl.
    unfold S.query_var.
    apply H.
    lia.
  + pose proof Nat.max_lub_l _ _ _ H0.
    pose proof Nat.max_lub_r _ _ _ H0.
    simpl in H1.
    destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite T.ceval_fold_right_CSeq in H2.
    rewrite !map_app, !fold_right_app in H2.
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2' [? ?]].
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2'' [? ?]].
    simpl in H5.
    rewrite (Rel_concat_id _ _ _ _ _) in H5.
    destruct H5.
    assert (forall X, X <= max_var_aexp a1 -> st1 X = st2 X)
           by (intros; apply H; lia).
    specialize (IHa1 _ _ _ _ _ _ H7 H3 TR
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H1)).
    assert (forall X, X <= max_var_aexp a2 -> st1 X = st2' X).
    {
      intros.
      rewrite H by lia.
      apply (proj1 IHa1).
      lia.
    }
    specialize (IHa2 (bg + op_count_aexp a1) _ _ _ _ _ H8
                     ltac:(lia) TR0
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H2)).
    split.
    - intros.
      rewrite (proj1 IHa1) by lia.
      rewrite (proj1 IHa2) by lia.
      apply H6.
      omega.
    - simpl.
      unfold ZFunc.add.
      rewrite H5.
      rewrite (proj2 IHa1), (proj2 IHa2).
      rewrite (proj1 IHa2) by (eapply translate_aexp_new_var_correct; eauto).
      auto.
  + pose proof Nat.max_lub_l _ _ _ H0.
    pose proof Nat.max_lub_r _ _ _ H0.
    simpl in H1.
    destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite T.ceval_fold_right_CSeq in H2.
    rewrite !map_app, !fold_right_app in H2.
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2' [? ?]].
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2'' [? ?]].
    simpl in H5.
    rewrite (Rel_concat_id _ _ _ _ _) in H5.
    destruct H5.
    assert (forall X, X <= max_var_aexp a1 -> st1 X = st2 X)
           by (intros; apply H; lia).
    specialize (IHa1 _ _ _ _ _ _ H7 H3 TR
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H1)).
    assert (forall X, X <= max_var_aexp a2 -> st1 X = st2' X).
    {
      intros.
      rewrite H by lia.
      apply (proj1 IHa1).
      lia.
    }
    specialize (IHa2 (bg + op_count_aexp a1) _ _ _ _ _ H8
                     ltac:(lia) TR0
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H2)).
    split.
    - intros.
      rewrite (proj1 IHa1) by lia.
      rewrite (proj1 IHa2) by lia.
      apply H6.
      omega.
    - simpl.
      unfold ZFunc.sub.
      rewrite H5.
      rewrite (proj2 IHa1), (proj2 IHa2).
      rewrite (proj1 IHa2) by (eapply translate_aexp_new_var_correct; eauto).
      auto.
  + pose proof Nat.max_lub_l _ _ _ H0.
    pose proof Nat.max_lub_r _ _ _ H0.
    simpl in H1.
    destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite T.ceval_fold_right_CSeq in H2.
    rewrite !map_app, !fold_right_app in H2.
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2' [? ?]].
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2'' [? ?]].
    simpl in H5.
    rewrite (Rel_concat_id _ _ _ _ _) in H5.
    destruct H5.
    assert (forall X, X <= max_var_aexp a1 -> st1 X = st2 X)
           by (intros; apply H; lia).
    specialize (IHa1 _ _ _ _ _ _ H7 H3 TR
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H1)).
    assert (forall X, X <= max_var_aexp a2 -> st1 X = st2' X).
    {
      intros.
      rewrite H by lia.
      apply (proj1 IHa1).
      lia.
    }
    specialize (IHa2 (bg + op_count_aexp a1) _ _ _ _ _ H8
                     ltac:(lia) TR0
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H2)).
    split.
    - intros.
      rewrite (proj1 IHa1) by lia.
      rewrite (proj1 IHa2) by lia.
      apply H6.
      omega.
    - simpl.
      unfold ZFunc.mul.
      rewrite H5.
      rewrite (proj2 IHa1), (proj2 IHa2).
      rewrite (proj1 IHa2) by (eapply translate_aexp_new_var_correct; eauto).
      auto.
Qed.

Lemma translate_bexp_correct: forall b bg st1 st2 st3 cs Y,
  (forall X, X <= max_var_bexp b -> st1 X = st2 X) ->
  max_var_bexp b <= bg ->
  translate_bexp b bg = (cs, Y) ->
  T.ceval (fold_right T.CSeq T.CSkip cs) st2 st3 ->
  (forall X, X <= bg -> st2 X = st3 X) /\ (S.beval b st1 <-> st3 Y = 1%Z) /\ (~ S.beval b st1 <-> st3 Y = 0%Z).
Proof.
  induction b; simpl max_var_bexp; intros.
  + simpl in H1.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite (Rel_concat_id _ _ _ _ _) in H2.
    destruct H2.
    split; [| split].
    - intros.
      apply H2; omega.
    - simpl.
      unfold S.beval.
      tauto.
    - simpl.
      unfold S.beval.
      split; [tauto | intros; omega].
  + simpl in H1.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite (Rel_concat_id _ _ _ _ _) in H2.
    destruct H2.
    split; [| split].
    - intros.
      apply H2; omega.
    - simpl.
      unfold S.beval.
      split; [tauto | intros; omega].
    - simpl.
      unfold S.beval.
      tauto.
  + pose proof Nat.max_lub_l _ _ _ H0.
    pose proof Nat.max_lub_r _ _ _ H0.
    simpl in H1.
    destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite T.ceval_fold_right_CSeq in H2.
    rewrite !map_app, !fold_right_app in H2.
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2' [? ?]].
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2'' [? ?]].
    simpl in H5.
    rewrite (Rel_concat_id _ _ _ _ _) in H5.
    destruct H5.
    assert (forall X, X <= max_var_aexp a1 -> st1 X = st2 X)
           by (intros; apply H; lia).
    specialize (translate_aexp_correct _ _ _ _ _ _ _ H7 H3 TR
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H1)) as IHa1.
    assert (forall X, X <= max_var_aexp a2 -> st1 X = st2' X).
    {
      intros.
      rewrite H by lia.
      apply (proj1 IHa1).
      lia.
    }
    specialize (translate_aexp_correct _ (bg + op_count_aexp a1) _ _ _ _ _ H8
                     ltac:(lia) TR0
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H2)) as IHa2.
    split.
    - intros.
      rewrite (proj1 IHa1) by lia.
      rewrite (proj1 IHa2) by lia.
      apply H6.
      omega.
    - simpl.
      unfold ZFunc.test_eq.
      rewrite H5.
      rewrite (proj2 IHa1), (proj2 IHa2).
      rewrite (proj1 IHa2) by (eapply translate_aexp_new_var_correct; eauto).
      destruct (st2'' Y1 =? st2'' Y2)%Z eqn:?H.
      * apply Z.eqb_eq in H9.
        split; [tauto | split; intros; [tauto | congruence]].
      * apply Z.eqb_neq in H9.
        split; [split; intros; [tauto | congruence] | tauto].
  + pose proof Nat.max_lub_l _ _ _ H0.
    pose proof Nat.max_lub_r _ _ _ H0.
    simpl in H1.
    destruct (translate_aexp a1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_aexp a2 (bg + op_count_aexp a1)) as [cs2 Y2] eqn:?TR.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite T.ceval_fold_right_CSeq in H2.
    rewrite !map_app, !fold_right_app in H2.
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2' [? ?]].
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2'' [? ?]].
    simpl in H5.
    rewrite (Rel_concat_id _ _ _ _ _) in H5.
    destruct H5.
    assert (forall X, X <= max_var_aexp a1 -> st1 X = st2 X)
           by (intros; apply H; lia).
    specialize (translate_aexp_correct _ _ _ _ _ _ _ H7 H3 TR
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H1)) as IHa1.
    assert (forall X, X <= max_var_aexp a2 -> st1 X = st2' X).
    {
      intros.
      rewrite H by lia.
      apply (proj1 IHa1).
      lia.
    }
    specialize (translate_aexp_correct _ (bg + op_count_aexp a1) _ _ _ _ _ H8
                     ltac:(lia) TR0
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H2)) as IHa2.
    split.
    - intros.
      rewrite (proj1 IHa1) by lia.
      rewrite (proj1 IHa2) by lia.
      apply H6.
      omega.
    - simpl.
      unfold ZFunc.test_le.
      rewrite H5.
      rewrite (proj2 IHa1), (proj2 IHa2).
      rewrite (proj1 IHa2) by (eapply translate_aexp_new_var_correct; eauto).
      destruct (st2'' Y1 <=? st2'' Y2)%Z eqn:?H.
      * apply Z.leb_le in H9.
        split; [tauto | split; intros; [tauto | congruence]].
      * apply Z.leb_gt in H9.
        split; [split; intros; [omega | congruence] | omega].
  + simpl in H1.
    destruct (translate_bexp b bg) as [cs1 Y1] eqn:?TR.
    injection H1 as ? ?; subst.
    rewrite T.ceval_fold_right_CSeq in H2.
    rewrite !map_app, !fold_right_app in H2.
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2' [? ?]].
    simpl in H2.
    rewrite (Rel_concat_id _ _ _ _ _) in H2.
    destruct H2.
    assert (forall X, X <= max_var_bexp b -> st1 X = st2 X)
           by (intros; apply H; lia).
    specialize (IHb _ _ _ _ _ _ H4 H0 TR
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H1)).
    split.
    - intros.
      rewrite (proj1 IHb) by lia.
      apply H3.
      omega.
    - simpl.
      unfold Sets.complement.
      rewrite H2.
      destruct (st2' Y1 =? 0)%Z eqn:?H.
      * apply Z.eqb_eq in H5.
        split; [tauto | split; intros; [tauto | congruence]].
      * apply Z.eqb_neq in H5.
        split; [split; intros; [tauto | congruence] | tauto].
  + pose proof Nat.max_lub_l _ _ _ H0.
    pose proof Nat.max_lub_r _ _ _ H0.
    simpl in H1.
    destruct (translate_bexp b1 bg) as [cs1 Y1] eqn:?TR.
    destruct (translate_bexp b2 (bg + op_count_bexp b1)) as [cs2 Y2] eqn:?TR.
    injection H1 as ? ?; subst.
    simpl in H2.
    rewrite T.ceval_fold_right_CSeq in H2.
    rewrite !map_app, !fold_right_app in H2.
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2' [? ?]].
    apply fold_right_concat_iff in H2.
    destruct H2 as [st2'' [? ?]].
    simpl in H5.
    rewrite (Rel_concat_id _ _ _ _ _) in H5.
    destruct H5.
    assert (forall X, X <= max_var_bexp b1 -> st1 X = st2 X)
           by (intros; apply H; lia).
    specialize (IHb1 _ _ _ _ _ _ H7 H3 TR
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H1)).
    assert (forall X, X <= max_var_bexp b2 -> st1 X = st2' X).
    {
      intros.
      rewrite H by lia.
      apply (proj1 IHb1).
      lia.
    }
    specialize (IHb2 (bg + op_count_bexp b1) _ _ _ _ _ H8
                     ltac:(lia) TR0
                     ltac:(rewrite T.ceval_fold_right_CSeq; apply H2)).
    split.
    - intros.
      rewrite (proj1 IHb1) by lia.
      rewrite (proj1 IHb2) by lia.
      apply H6.
      omega.
    - simpl.
      rewrite H5.
      rewrite (proj1 IHb2) in IHb1 by (eapply translate_bexp_new_var_correct; eauto).
      destruct (classic (S.beval b1 st1)) as [HH1 | HH1];
        [ pose proof proj1 (proj1 (proj2 IHb1)) HH1
        | pose proof proj1 (proj2 (proj2 IHb1)) HH1];
      (destruct (classic (S.beval b2 st1)) as [HH2 | HH2];
        [ pose proof proj1 (proj1 (proj2 IHb2)) HH2
        | pose proof proj1 (proj2 (proj2 IHb2)) HH2]);
      rewrite H9, H10; simpl;
      first [ split; [tauto | split; intros; [tauto | congruence]]
            | split; [split; intros; [tauto | congruence] | tauto]].
Qed.

Lemma translate_com_correct: forall c bg st1 st2 st3 st4 c',
  (forall X, X <= max_var_com c -> st1 X = st2 X) ->
  max_var_com c <= bg ->
  translate_com c bg = c' ->
  S.ceval c st1 st3 ->
  T.ceval c' st2 st4 ->
  (forall X, X <= bg -> st3 X = st4 X).
Proof.
  induction c.
  + intros.
    simpl in H1.
    subst.
    simpl in H2, H3.
    unfold Rel.id.
Abort.
