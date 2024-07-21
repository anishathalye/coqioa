Require Import IOA.
Require Import Automation.
Require Import Simulation.
Require Import Misc.

Require Import Eqdep.
Require Import List.
Import ListNotations.

Theorem refines_self :
  forall T (def : AutomatonDef T), refines def def.
Proof.
  unfold refines; auto.
Qed.

Theorem refines_comp_comm :
  forall (EA EB Ext : Type)
         (A : AutomatonDef EA) (B : AutomatonDef EB)
         (mapA : Ext -> option EA) (mapB : Ext -> option EB),
    refines
      (compose A B Ext mapA mapB)
      (compose B A Ext mapB mapA).
Proof.
  intros ? ? ? ? ? mapA mapB.
  apply forward_simulation with (fun st st' =>
                                   (fst st) = (snd st') /\
                                   (snd st) = (fst st')).
  split.
  - intros [? ?] [? ?].
    eexists (_, _); intuition; split; auto.
  - intros s1' [? ?] ? s2' ? [HrelA HrelB].
    eexists (_, _); intuition.
    destruct act1 as [int | ext].
    + destruct int;
        eapply Step_Internal; simpl in *; eauto; rewrite <- HrelA, <- HrelB; solve_match.
    + eapply Step_External; simpl in *; eauto;
        destruct (mapA _); destruct (mapB _); destruct s1'; destruct s2'; shallow.
Qed.

Lemma valid_execution_frag_comp :
  forall EA EB (defA : AutomatonDef EA) (defB : AutomatonDef EB) ExtType
         (convA : ExtType -> option EA)
         (convB : ExtType -> option EB)
         init final,
  forall acts,
    valid_execution_fragment
      (compose defA defB ExtType convA convB)
      init final acts ->
    valid_execution_fragment defA (fst init) (fst final) (flatmap convA acts) /\
    valid_execution_fragment defB (snd init) (snd final) (flatmap convB acts).
Proof.
  intros ? ? ? ? ? convA convB ? ? ? Hvalid.
  induction Hvalid; try solve [subst; intuition; eauto]; simpl in *.
  - destruct int; intuition;
      solve [eapply Step_Internal; eauto] || solve [rw; eauto].
  - destruct (convA ext); destruct (convB ext); intuition;
      solve [eapply Step_External; eauto] || solve [rw; eauto].
Qed.

Lemma valid_execution_frag_comp_join_nil :
  forall EA EB (defA : AutomatonDef EA) (defB : AutomatonDef EB) ExtType
         (convA : ExtType -> option EA)
         (convB : ExtType -> option EB)
         initA initB finalA finalB,
    valid_execution_fragment defA initA finalA nil /\
    valid_execution_fragment defB initB finalB nil ->
    valid_execution_fragment
      (compose defA defB ExtType convA convB)
      (initA, initB)
      (finalA, finalB)
      nil.
Proof.
  intros; cleanup;
    induction_vef; induction_vef; subst; intuition; try discriminate;
      eapply Step_Internal; eauto; solve_match.
Qed.

Hint Resolve valid_execution_frag_comp_join_nil.

Lemma valid_execution_frag_comp_join_single_both :
  forall EA EB ExtType (defA : AutomatonDef EA) (defB : AutomatonDef EB)
         convA convB initA initB finalA finalB e eA eB,
    valid_execution_fragment defA initA finalA (eA :: nil) ->
    valid_execution_fragment defB initB finalB (eB :: nil) ->
    convA e = Some eA ->
    convB e = Some eB ->
    valid_execution_fragment
      (compose defA defB ExtType convA convB)
      (initA, initB)
      (finalA, finalB)
      (e :: nil).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? HvalidA HvalidB.
  induction_vef HvalidA; intuition; try discriminate.
  - induction_vef HvalidB; subst; intuition; try discriminate;
      eapply Step_Internal; simpl; eauto; solve_match.
  - clear IHHvalidA; induction_vef HvalidB; cleanup; subst; intuition; try discriminate.
    + eapply Step_Internal; simpl; eauto; solve_match.
    + estep_ext_break; simpl; repeat simpl_match; eauto.
Qed.

Hint Resolve valid_execution_frag_comp_join_single_both.

Lemma valid_execution_frag_comp_join_single_left :
  forall EA EB ExtType (defA : AutomatonDef EA) (defB : AutomatonDef EB)
         convA convB initA initB finalA finalB e eA,
    valid_execution_fragment defA initA finalA (eA :: nil) ->
    valid_execution_fragment defB initB finalB nil ->
    convA e = Some eA ->
    convB e = None ->
    valid_execution_fragment
      (compose defA defB ExtType convA convB)
      (initA, initB)
      (finalA, finalB)
      (e :: nil).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? HvalidA HvalidB.
  induction_vef HvalidA; intuition; try discriminate.
  - induction_vef HvalidB; subst; intuition; try discriminate;
      eapply Step_Internal; simpl; eauto; solve_match.
  - clear IHHvalidA; induction_vef HvalidB; cleanup; subst; intuition; try discriminate;
      estep_ext_break; simpl; repeat simpl_match; eauto.
Qed.

Hint Resolve valid_execution_frag_comp_join_single_left.

Lemma valid_execution_frag_comp_join_single_right :
  forall EA EB ExtType (defA : AutomatonDef EA) (defB : AutomatonDef EB)
         convA convB initA initB finalA finalB e eB,
    valid_execution_fragment defA initA finalA nil ->
    valid_execution_fragment defB initB finalB (eB :: nil) ->
    convA e = None ->
    convB e = Some eB ->
    valid_execution_fragment
      (compose defA defB ExtType convA convB)
      (initA, initB)
      (finalA, finalB)
      (e :: nil).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? HvalidA HvalidB.
  induction_vef HvalidB; intuition; try discriminate.
  - induction_vef HvalidA; subst; intuition; try discriminate;
      eapply Step_Internal; simpl; eauto; solve_match.
  - clear IHHvalidB; induction_vef HvalidA; cleanup; subst; intuition; try discriminate;
      estep_ext_break; simpl; repeat simpl_match; eauto.
Qed.

Hint Resolve valid_execution_frag_comp_join_single_right.

Lemma valid_execution_frag_comp_join_single_none :
  forall EA EB ExtType (defA : AutomatonDef EA) (defB : AutomatonDef EB)
         convA convB initA initB finalA finalB e,
    valid_execution_fragment defA initA finalA nil ->
    valid_execution_fragment defB initB finalB nil ->
    convA e = None ->
    convB e = None ->
    valid_execution_fragment
      (compose defA defB ExtType convA convB)
      (initA, initB)
      (finalA, finalB)
      (e :: nil).
Proof.
  intros; eapply Step_External; simpl; repeat simpl_match; eauto.
Qed.

Hint Resolve valid_execution_frag_comp_join_single_none.

Lemma valid_execution_frag_comp_join :
  forall EA EB (defA : AutomatonDef EA) (defB : AutomatonDef EB) ExtType
         (convA : ExtType -> option EA)
         (convB : ExtType -> option EB)
         initA initB finalA finalB,
  forall acts,
    valid_execution_fragment defA initA finalA (flatmap convA acts) /\
    valid_execution_fragment defB initB finalB (flatmap convB acts) ->
    valid_execution_fragment
      (compose defA defB ExtType convA convB)
      (initA, initB)
      (finalA, finalB)
      acts.
Proof.
  intros ? ? defA defB ? convA convB initA initB finalA finalB acts.
  generalize dependent finalB.
  generalize dependent finalA.
  generalize dependent initB.
  generalize dependent initA.
  induction acts; auto.
  intros; cleanup;
    simpl in *.
  destruct (convA _) eqn:?; destruct (convB _) eqn:?;
           repeat split_execution;
    eapply valid_execution_fragment_join_single with (_, _); eauto.
Qed.

Hint Resolve valid_execution_frag_comp_join.

Theorem refines_comp_subst :
  forall (EA EB Ext : Type)
         (A A' : AutomatonDef EA) (B : AutomatonDef EB)
         (mapA : Ext -> option EA) (mapB : Ext -> option EB),
    refines A' A ->
    refines
      (compose A' B Ext mapA mapB)
      (compose A B Ext mapA mapB).
Proof.
  intros ? ? ? ? ? ? mapA mapB.
  intros Hrefines.
  unfold refines.
  intros acts [init' [final' [[HstartA' HstartB] Hfrag']]].
  specialize (Hrefines (flatmap mapA acts)).
  pose proof (valid_execution_frag_comp _ _ _ _ _ _ _ _ _ _ Hfrag') as [HfragA' HfragB].
  specialize (Hrefines ltac:(repeat eexists; eauto)).
  destruct Hrefines as [initA [finalA [HstartA HfragA]]].
  unfold in_traces.
  do 2 eexists; ebreak_compstate; split; [split|]; eauto.
Qed.

Theorem refines_comp_subst_r :
  forall EA EB Ext (A A' : AutomatonDef EA) (B : AutomatonDef EB) mapA mapB,
    refines A' A ->
    refines
      (compose B A' Ext mapA mapB)
      (compose B A Ext mapA mapB).
Proof.
  intros.
  eapply refines_trans.
  eapply refines_comp_comm.
  eapply refines_trans.
  eapply refines_comp_subst; eauto.
  eapply refines_comp_comm.
Qed.

Theorem refines_property :
  forall E (defA defA' : AutomatonDef E) (P : list E -> Prop),
    (forall trace, in_traces defA trace -> P trace) ->
    refines defA' defA ->
    (forall trace, in_traces defA' trace -> P trace).
Proof.
  eauto.
Qed.

Inductive interspersed {I E : Type} : list E -> list (I + E) -> Prop :=
| interspersed_nil : interspersed [] []
| interspersed_here : forall e es ls,
    interspersed es ls ->
    interspersed (e :: es) (inr e :: ls)
| interspersed_skip : forall i es ls,
    interspersed es ls ->
    interspersed es (inl i :: ls)
.

Hint Constructors interspersed.

Definition interspersed_conv {I E T : Type} (mapI : I -> T) (mapE : E -> T) (ls : list (I + E)) : list T :=
  let f := fun a => match a with
                    | inl i => mapI i
                    | inr e => mapE e
                    end in
  map f ls.

Lemma frag_rename_interspersed :
  forall T (A : AutomatonDef T) E fE I fI init final racts,
    valid_execution_fragment (rename A E fE I fI) init final racts ->
    (exists acts,
        valid_execution_fragment A init final (interspersed_conv fI fE acts) /\
        interspersed racts acts).
Proof.
  intros T A E fE I fI init final racts H.
  induction H.
  - eexists; split; simpl; eauto.
    subst; simpl; eauto.
  - destruct int.
    + destruct IHvalid_execution_fragment as [acts' [? ?]].
      exists acts'.
      split; eauto.
      eapply Step_Internal; simpl in *; eauto.
    + destruct IHvalid_execution_fragment as [acts' [? ?]].
      exists (inl i :: acts').
      split; eauto.
      eapply Step_External; eauto.
      eauto.
  - destruct IHvalid_execution_fragment as [acts' [? ?]].
    exists (inr ext :: acts').
    split; eauto.
    simpl.
    eapply valid_execution_fragment_join_single; eauto.
    eapply Step_External; eauto.
    eauto.
Qed.

Lemma in_traces_rename_interspersed :
  forall T (A : AutomatonDef T) E fE I fI racts,
    in_traces (rename A E fE I fI) racts ->
    (exists acts, in_traces A (interspersed_conv fI fE acts) /\
                  interspersed racts acts).
Proof.
  intros T A E fE I fI racts H.
  destruct H as [init [final [Hstart Hfrag]]].
  destruct (frag_rename_interspersed _ _ _ _ _ _ _ _ _ Hfrag) as [acts [? ?]].
  exists acts.
  repeat eexists; eauto.
Qed.

Lemma step_empty_rename :
  forall T (A : AutomatonDef T) E fE I fI init final,
    valid_execution_fragment A init final [] ->
    valid_execution_fragment (rename A E fE I fI) init final [].
Proof.
  intros T A E fE I fI init final H.
  induction_vef; eauto; try congruence.
  eapply Step_Internal with _ (inl int); eauto.
  eauto.
Qed.

Lemma frag_interspersed_rename :
  forall T (A : AutomatonDef T) E fE I fI init final racts acts,
    valid_execution_fragment A init final (interspersed_conv fI fE acts) ->
    interspersed racts acts ->
    valid_execution_fragment (rename A E fE I fI) init final racts.
Proof.
  intros T A E fE I fI init final racts acts Hvalid Hint.
  generalize dependent Hvalid.
  generalize dependent final.
  generalize dependent init.
  induction Hint.
  - intros; simpl in *; eauto using step_empty_rename.
  - intros init final Hfrag.
    simpl in *.
    apply valid_execution_fragment_consume in Hfrag.
    destruct Hfrag as [s' [Hfragl Hfragr]].
    eapply valid_execution_fragment_join_single; eauto.
    clear es ls Hint IHHint final Hfragr.
    induction_vef; try congruence; subst; intuition.
    + eapply Step_Internal with _ (inl int); simpl; eauto.
    + inversion Heql; subst.
      eapply Step_External; [| apply step_empty_rename; eauto]; eauto.
  - intros init final Hfrag.
    simpl in *.
    apply valid_execution_fragment_consume in Hfrag.
    destruct Hfrag as [s' [Hfragl Hfragr]].
    replace es with ([] ++ es) by auto.
    eapply valid_execution_fragment_join; [| apply IHHint; eauto].
    clear ls es Hint IHHint final Hfragr.
    induction_vef; try congruence; subst; intuition.
    + eapply Step_Internal with _ (inl int); simpl; eauto.
    + inversion Heql; subst.
      eapply Step_Internal with _ (inr i); simpl; eauto.
      apply step_empty_rename; auto.
Qed.

Lemma in_traces_interspersed_rename :
  forall T (A : AutomatonDef T) E fE I fI racts acts,
    in_traces A (interspersed_conv fI fE acts) ->
    interspersed racts acts ->
    in_traces (rename A E fE I fI) racts.
Proof.
  intros T A E fE I fI racts acts Htrace Hint.
  destruct Htrace as [init [final [? ?]]].
  exists init; exists final; intuition.
  eapply frag_interspersed_rename; eauto.
Qed.

Theorem refines_rename :
  forall T (A' A : AutomatonDef T) E fE I fI,
    refines A' A ->
    refines (rename A' E fE I fI) (rename A E fE I fI).
Proof.
  intros T A' A E fE I fI H.
  intros racts Htrace.
  pose proof (in_traces_rename_interspersed _ _ _ _ _ _ _ Htrace); cleanup.
  eapply in_traces_interspersed_rename; eauto.
Qed.
