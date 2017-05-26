Require Import Automation.
Require Import Misc.

Require Import List.

Record AutomatonDef (ExternalActionType : Type) :=
  mkAutomatonDef {
      StateType : Type;
      InternalActionType : Type;
      start : StateType -> Prop;
      transition : StateType ->
                   (InternalActionType + ExternalActionType) ->
                   StateType ->
                   Prop;
    }.

Arguments InternalActionType {ExternalActionType}.
Arguments StateType {ExternalActionType}.
Arguments start {ExternalActionType}.
Arguments transition {ExternalActionType}.

(* parameterized automaton def : params are additional constraints on
start state *)
Definition parameterize {E : Type} (def : AutomatonDef E) (param : def.(StateType) -> Prop) :=
  mkAutomatonDef
    E
    _
    _
    (fun st => def.(start) st /\ param st)
    def.(transition).

Arguments parameterize {E}.

Definition liftExternal {A B : Type} (rel : A -> B -> A -> Prop) (st : A) (act : EmptySet + B) (st' : A) : Prop :=
  match act with
  | inl act' => match act' with end
  | inr act' => rel st act' st'
  end.

(* hiding and renaming can both be done with rename *)

Section Rename.

  Variable ExternalActionType : Type.
  Variable def : AutomatonDef ExternalActionType.
  Variable NewExternalActionType : Type.
  Variable conv_ext : NewExternalActionType -> ExternalActionType.
  Variable HiddenActionType : Type.
  Variable conv_hid : HiddenActionType -> ExternalActionType.

  Definition Rename_InternalActionType : Type := def.(InternalActionType) + HiddenActionType.
  Definition Rename_ActionType : Type := Rename_InternalActionType + NewExternalActionType.

  Definition Rename_transition (st : def.(StateType)) (act : Rename_ActionType) (st' : def.(StateType)) :=
    match act with
    | inl (inl act') => def.(transition) st (inl act') st'
    | inl (inr act') => def.(transition) st (inr (conv_hid act')) st'
    | inr act' => def.(transition) st (inr (conv_ext act')) st'
    end.

  Definition rename : AutomatonDef NewExternalActionType :=
    mkAutomatonDef
      _
      (StateType def)
      _
      (start def)
      Rename_transition.

End Rename.

Arguments rename {ExternalActionType}.

Section Composition.

  Variable E1 E2 : Type.
  Variable a1 : AutomatonDef E1.
  Variable a2 : AutomatonDef E2.
  Variable Comp_ExternalActionType : Type.
  Variable actiontype_conv1 : Comp_ExternalActionType -> option E1.
  Variable actiontype_conv2 : Comp_ExternalActionType -> option E2.
  Definition Comp_InternalActionType : Type :=
    a1.(InternalActionType) + a2.(InternalActionType).
  Definition Comp_ActionType : Type :=
    Comp_InternalActionType + Comp_ExternalActionType.

  Definition Comp_StateType : Type := a1.(StateType) * a2.(StateType).

  Definition Comp_start (st : Comp_StateType) : Prop :=
    a1.(start) st.(fst) /\ a2.(start) st.(snd).

  Definition Comp_transition (st : Comp_StateType) (act : Comp_ActionType) (st' : Comp_StateType) : Prop :=
    match act with
    | inl act_int =>
      match act_int with
      | inl act_int_1 =>
        a1.(transition) st.(fst) (inl act_int_1) st'.(fst) /\
        st.(snd) = st'.(snd)
      | inr act_int_2 =>
        a2.(transition) st.(snd) (inl act_int_2) st'.(snd) /\
        st.(fst) = st'.(fst)
      end
    | inr act_ext =>
      let oact1 := actiontype_conv1 act_ext in
      let oact2 := actiontype_conv2 act_ext in
      match oact1, oact2 with
      | Some act1, Some act2 =>
        a1.(transition) st.(fst) (inr act1) st'.(fst) /\
        a2.(transition) st.(snd) (inr act2) st'.(snd)
      | Some act1, None =>
        a1.(transition) st.(fst) (inr act1) st'.(fst) /\
        st.(snd) = st'.(snd)
      | None, Some act2 =>
        a2.(transition) st.(snd) (inr act2) st'.(snd) /\
        st.(fst) = st'.(fst)
      | None, None =>
        st' = st
      end
    end.

  Definition compose : AutomatonDef Comp_ExternalActionType :=
    mkAutomatonDef
      _
      Comp_StateType
      Comp_InternalActionType
      Comp_start
      Comp_transition.

End Composition.

Arguments compose {E1 E2}.

Ltac inst_rec_compstate T cont :=
  lazymatch eval simpl in T with
  | Comp_StateType _ _ ?A ?B =>
    inst_rec_compstate
      (StateType A)
      ltac:(fun left =>
              inst_rec_compstate
                (StateType B)
                ltac:(fun right => cont (left, right)))
  | _ => let x := fresh "x" in
         evar (x : T); cont x; clear x
  end.

Ltac ebreak_compstate :=
  repeat match goal with
  | [ |- context[ ?x ] ] =>
    is_evar x;
    let T := type of x in
    (* we check the type here even though it happens in
       inst_rec_compstate, because we want the ebreak_compstate top
       level repeat to get all the separate evars but we don't want it
       to loop forever *)
    lazymatch eval simpl in T with
    | Comp_StateType _ _ _ _ => inst_rec_compstate T ltac:(fun x' => unify x x')
    end
  end.

Ltac destruct_compstate :=
  repeat match goal with
         | [ st : StateType _ |- _ ] =>
           let T := type of st in
           lazymatch eval simpl in T with
           | Comp_StateType _ _ _ _ => destruct st
           end
         end.

Definition automaton_step {T} (def : AutomatonDef T) s1 action s2 : Prop :=
  def.(transition) s1 action s2.

Inductive valid_execution_fragment {T} (def : AutomatonDef T) (st st' : def.(StateType)) : list T -> Prop :=
| Step_None :
    st = st' ->
    valid_execution_fragment _ st st' nil
| Step_Internal : forall st'' acts (int : def.(InternalActionType)),
    automaton_step _ st (inl int) st'' ->
    valid_execution_fragment _ st'' st' acts ->
    valid_execution_fragment _ st st' acts
| Step_External : forall st'' acts (ext : T),
    automaton_step _ st (inr ext) st'' ->
    valid_execution_fragment _ st'' st' acts ->
    valid_execution_fragment _ st st' (ext :: acts).

Hint Constructors valid_execution_fragment.

Ltac induction_vef H :=
  let T := type of H in
  match T with
  | valid_execution_fragment _ _ _ ?l => match l with
                                         | (_ :: _) => remember l
                                         | nil => remember l
                                         | _ => idtac
                                         end; induction H
  | _ => fail "not a valid execution fragment"
  end.

Tactic Notation "induction_vef" ident(H) := induction_vef H.
Tactic Notation "induction_vef" :=
  match goal with
  | [ H : valid_execution_fragment _ _ _ _ |- _ ] => induction_vef H
  end.

Tactic Notation "estep_ext_break" :=
  match goal with
  | [ |- valid_execution_fragment ?def _ _ _ ] =>
    eapply Step_External;
    ebreak_compstate
  end.

(* note: this is a tactic notation because we want int_act to be an untyped term *)
Tactic Notation "estep_int_break" uconstr(int) :=
  match goal with
  | [ |- valid_execution_fragment ?def _ _ _ ] =>
    eapply Step_Internal with _ int;
    ebreak_compstate
  end.

Lemma valid_execution_fragment_join : forall {T} (def : AutomatonDef T) (s s' s'' : def.(StateType)) a a',
    valid_execution_fragment _ s s' a ->
    valid_execution_fragment _ s' s'' a' ->
    valid_execution_fragment _ s s'' (a ++ a').
Proof.
  induction 1; subst; simpl; intros; eauto.
Qed.

Lemma valid_execution_fragment_join' : forall {T} (def : AutomatonDef T) (s s' s'' : def.(StateType)) a a' a'',
    valid_execution_fragment _ s s' a ->
    valid_execution_fragment _ s' s'' a' ->
    a'' = a ++ a' ->
    valid_execution_fragment _ s s'' a''.
Proof.
  intros; subst; eauto using valid_execution_fragment_join.
Qed.

Hint Resolve valid_execution_fragment_join'.

Lemma valid_execution_fragment_join_single : forall {T} (def : AutomatonDef T) (s s' s'' : def.(StateType)) a acts,
    valid_execution_fragment _ s s' (a :: nil) ->
    valid_execution_fragment _ s' s'' acts ->
    valid_execution_fragment _ s s'' (a :: acts).
Proof.
  eauto.
Qed.

Lemma valid_execution_fragment_consume :
  forall {T} (def : AutomatonDef T) (s s'' : def.(StateType)) act acts,
    valid_execution_fragment _ s s'' (act :: acts) ->
    exists s',
      valid_execution_fragment _ s s' (act :: nil) /\
      valid_execution_fragment _ s' s'' (acts).
Proof.
  intros; induction_vef; subst; try congruence; intuition;
    cleanup; subst; eauto.
Qed.

Ltac split_execution :=
  match goal with
  | [ H : valid_execution_fragment _ _ _ (_ :: ?l) |- _ ] =>
    lazymatch l with
    | nil => fail
    | _ => idtac
    end;
    pose proof (valid_execution_fragment_consume _ _ _ _ _ H) as [? [? ?]];
    clear H
  end.

Lemma valid_execution_fragment_split : forall {T} (def : AutomatonDef T) (s s'' : def.(StateType)) a a',
    valid_execution_fragment _ s s'' (a ++ a') ->
    exists s',
      valid_execution_fragment _ s s' a /\
      valid_execution_fragment _ s' s'' a'.
Proof.
  intros T def s s'' a a' H.
  generalize dependent a'.
  generalize dependent s.
  generalize dependent s''.
  induction a; eauto.
  intros.
  pose proof (valid_execution_fragment_consume _ _ _ _ _ H) as Hcons.
  inversion Hcons as [? [? Hintr]].
  specialize (IHa _ _ _ Hintr).
  inversion IHa; eexists; intuition; eauto.
Qed.

Definition in_traces {T} (def : AutomatonDef T) acts :=
  exists init final, def.(start) init /\ valid_execution_fragment def init final acts.

Definition reachable {T} (def : AutomatonDef T) st :=
  exists init acts, def.(start) init /\ valid_execution_fragment def init st acts.

Definition invariant {T} (def : AutomatonDef T) (P : def.(StateType) -> Prop) :=
  forall st, reachable def st -> P st.

Definition invariant_ind {T} (def : AutomatonDef T) (P : def.(StateType) -> Prop) :=
  (forall st, def.(start) st -> P st) /\
  (forall st st' act,
      P st ->
      automaton_step def st act st' ->
      P st').

Lemma invariant_ind_vef_step :
  forall T (def : AutomatonDef T) (P : def.(StateType) -> Prop) st acts st',
    P st ->
    (forall st st' act,
        P st ->
        automaton_step def st act st' ->
        P st') ->
    valid_execution_fragment def st st' acts ->
    P st'.
Proof.
  intros; induction_vef; subst; eauto.
Qed.

(* note: the converse is not true *)
Lemma invariant_ind_impl_invariant :
  forall T (def : AutomatonDef T) P,
    invariant_ind def P -> invariant def P.
Proof.
  unfold invariant_ind; unfold invariant; unfold reachable; intros; cleanup.
  eapply invariant_ind_vef_step; eauto.
Qed.

Ltac invariant_ind :=
  match goal with
  | [ |- invariant ?def ?P ] => apply invariant_ind_impl_invariant; split
  end.

Lemma in_traces_extend :
  forall T (def : AutomatonDef T) act acts,
    in_traces def (acts ++ (act :: nil)) ->
    in_traces def acts.
Proof.
  intros T def act acts.
  intros [init [final [Hstart Hvalid]]].
  exists init.
  pose proof (valid_execution_fragment_split
                _
                init
                final
                acts
                (act :: nil)
                Hvalid) as [int [Hint Hintr]].
  exists int.
  split; auto.
Qed.

Definition refines
           {T : Type}
           (def1 def2 : AutomatonDef T) : Prop :=
  forall acts,
    in_traces def1 acts ->
    in_traces def2 acts.
