Require Import ClassicalFacts.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationPairs.
Require Import VCF.BoubakiWitt.
Require Import VCF.KnasterTarski.

Definition Two_dimensions_fixpoint
             {A B}
             {RA RA': A -> A -> Prop}
             {RB RB': B -> B -> Prop}
             {limit bot} 
             {CPO: CompletePartialOrder_Setoid RA RA' limit bot}
             {lub} 
             {CL: CompleteLattice_Setoid RB RB' lub} 
             (f: A -> A) (g: A -> B -> B): A*B :=
             ((BW_fix f), KT_fix_l (fun b => g (BW_fix f) b)).
             
Definition Two_dimensions_R' 
            {A B}
            {RA': A -> A -> Prop}
            {RB': B -> B -> Prop}:(A*B) -> (A*B) -> Prop:=
            fun x y => RA' (fst x) (fst y) /\ RB' (snd x) (snd y).
            

Inductive  Two_dimensions_R
            {A B}
            {RA: A -> A -> Prop}
            {RB: B -> B -> Prop}: A*B -> A*B -> Prop:=
          |T_d_fst_same: forall c1 c2,
              RA (fst c1) (fst c2) ->
              RA (fst c2) (fst c1) ->
              RB (snd c1) (snd c2) ->
              Two_dimensions_R c1 c2
          |T_d_fst_diff: forall c1 c2,
              RA (fst c1) (fst c2) ->
              (~ RA (fst c2) (fst c1)) ->
              Two_dimensions_R c1 c2.

Theorem Two_dimension_theorem
            {A B}
            {RA RA': A -> A -> Prop}
            {RB RB': B -> B -> Prop}
            {Equ1: Equivalence RA'}
            {Equ2: Equivalence RB'}
            {limit bot} 
            {CPO: CompletePartialOrder_Setoid RA RA' limit bot}
            {lub} 
            {CL: CompleteLattice_Setoid RB RB' lub} 
            (f: A -> A)
            (g: A -> B -> B):
            Proper (RA ==> RA) f ->
            seq_continuous RA RA' limit f ->
            (forall a:A, Proper (RB ==> RB) (fun b : B => g a b)) ->
            @Two_dimensions_R' _ _ RA' RB' 
            (Two_dimensions_fixpoint f g) 
            (f (fst (Two_dimensions_fixpoint f g)),
             g (fst (Two_dimensions_fixpoint f g)) (snd (Two_dimensions_fixpoint f g))).
Proof.
  unfold Two_dimensions_R';split;simpl.
  - apply BourbakiWitt_fixpoint;eauto.
  - apply KnasterTarski_fixpoint_theorem_l;eauto.
Qed.

Theorem Two_dimensions_least_fixpoint
            {A B}
            {RA RA': A -> A -> Prop}
            {RB RB': B -> B -> Prop}
            {Equ1: Equivalence RA'}
            {Equ2: Equivalence RB'}
            {limit bot} 
            {CPO: CompletePartialOrder_Setoid RA RA' limit bot}
            {lub} 
            {CL: CompleteLattice_Setoid RB RB' lub} 
            (f: A -> A)
            (g: A -> B -> B):
            Proper (RA ==> RA) f ->
            Proper (RA' ==> RB' ==> RB') g ->
            seq_continuous RA RA' limit f ->
            (forall a:A, Proper (RB ==> RB) (fun b : B => g a b)) ->
            least_fixpoint (fun c => (f (fst c), g (fst c) (snd c))) 
            (@Two_dimensions_R _ _ RA RB) (@Two_dimensions_R' _ _ RA' RB')
            (Two_dimensions_fixpoint f g) .
Proof.
  intros.
  pose proof BourbakiWitt_least_fixpoint.
  unfold least_fixpoint;split.
  - apply Two_dimension_theorem;[apply H |apply H1| apply H2].
  - intros. unfold Two_dimensions_fixpoint.
    destruct a'. pose proof classic (RA a (BW_fix f)).
    destruct H5.
    + apply T_d_fst_same;simpl;eauto.
      { apply H3;[apply H| apply H1|destruct H4;eauto]. }
      assert(H6:RA (BW_fix f) a).
      { apply H3;[apply H| apply H1| destruct H4;eauto]. }
       apply KnasterTarski_fixpoint_least_fixpoint.
        apply H2. destruct H4.
        simpl in H6. simpl in H4.
      assert(RA' (BW_fix f) a). {
        pose proof CPO_PartialOrder.
        destruct H8.
        unfold BoubakiWitt.AntiSymmetric_Setoid in
        PO_AntiSymmetric_Setoid.
        apply PO_AntiSymmetric_Setoid;eauto.
      }
      simpl in H6,H7.
      unfold Proper,respectful in H1,H0.
      assert(RB' b b). {apply Equivalence_Reflexive. }
      specialize (H0 _ _ H8 _ _ H9).
      apply Equivalence_Symmetric in H0.
      apply (Equivalence_Transitive _ _ _ H7 H0).
    +apply T_d_fst_diff;simpl;eauto.
     apply H3. apply H. apply H1. destruct H4;eauto. 
Qed.