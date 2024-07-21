Require Import IOA.
Require Import Misc.
Require Import ListOps.
Require Import Simulation.
Require Import Automation.

Require Import Lia.
Require Import List.
Require Import Permutation.
Import ListNotations.

Module Channel.

  Section Main.

    Variable T : Type.

    Inductive ChannelSenderAPI :=
    | Send : T -> ChannelSenderAPI.
    Inductive ChannelReceiverAPI :=
    | Recv : T -> ChannelReceiverAPI.
    Definition ChannelAPI : Type := ChannelSenderAPI + ChannelReceiverAPI.

    Definition Reliable : AutomatonDef ChannelAPI :=
      mkAutomatonDef
        ChannelAPI
        (list T) (* state: list of messages *)
        EmptySet
        (fun st => st = []) (* start: buffer starts out empty *)
        (* transition relation: *)
        (fun st act st' =>
           match act with
           | inl e => match e with end
           | inr (inl (Send m)) => st' = st ++ [m]
           | inr (inr (Recv m)) => st = m :: st'
           end).

    Definition ReliableReordering : AutomatonDef ChannelAPI :=
      mkAutomatonDef
        ChannelAPI
        (list T) (* state: list of messages *)
        EmptySet
        (fun st => st = []) (* start: buffer starts out empty *)
        (* transition relation: *)
        (fun st act st' =>
           match act with
           | inl e => match e with end
           | inr (inl (Send m)) => st' = st ++ [m]
           | inr (inr (Recv m)) => removed m st st' (* can receive any message *)
           end).

  End Main.

  Arguments Send {T}.
  Arguments Recv {T}.

  Goal in_traces (Reliable _)
       [inl (Send 1); inl (Send 2); inr (Recv 1); inr (Recv 2)].
  Proof.
    unfold in_traces; do 2 eexists; split; [cbv; eauto |].
    repeat (estep_ext_break; simpl; auto).
  Qed.

  Goal in_traces (ReliableReordering _)
       [inl (Send 1); inl (Send 2); inr (Recv 2); inr (Recv 1)].
  Proof.
    unfold in_traces; do 2 eexists; split; [cbv; eauto |].
    repeat (estep_ext_break; simpl; intuition); eauto.
  Qed.

  Section ReorderingMediator.

    Variable T : Type. (* message type *)

    (* input from world, output to channel *)
    Definition ReorderingSendMediator :
      AutomatonDef (ChannelSenderAPI T + ChannelSenderAPI (nat * T)) :=
      mkAutomatonDef
        _
        (nat * list (nat * T)) (* state: next sequence number, message buffer *)
        EmptySet
        (fun st => st = (0, [])) (* start: seq=0, empty buffer *)
        (fun st act st' =>
           match act with
           | inl e => match e with end
           | inr (inl (Send m)) =>
             (* enqueue message tagged with sequence number in local buffer *)
             st' = (fst st + 1, snd st ++ [(fst st, m)])
           | inr (inr (Send (c, m))) =>
             (* send buffered message over channel *)
             fst st' = fst st /\ removed (c, m) (snd st) (snd st')
           end).

    (* input from channel, output to world *)
    Definition ReorderingReceiveMediator :
      AutomatonDef (ChannelReceiverAPI (nat * T) + ChannelReceiverAPI T) :=
      mkAutomatonDef
        _
        (nat * list (nat * T)) (* state: next sequence number, message buffer *)
        EmptySet
        (fun st => st = (0, [])) (* start: seq=0, empty buffer *)
        (fun st act st' =>
           match act with
           | inl e => match e with end
           | inr (inl (Recv (c, m))) =>
             (* enqueue message *)
             st' = (fst st, snd st ++ [(c, m)])
           | inr (inr (Recv m)) =>
             (* deliver message with the current sequence number *)
             fst st' = fst st + 1 /\ removed (fst st, m) (snd st) (snd st')
           end).

    Definition SendMediator_Channel :=
      compose
        ReorderingSendMediator
        (ReliableReordering (nat * T))
        (ChannelSenderAPI T + ChannelAPI (nat * T))
        (fun act => match act with
                    | inl act' => Some (inl act')
                    | inr act' => match act' with
                                  | inl act'' => Some (inr act'')
                                  | inr _ => None
                                  end
                    end)
        (fun act => match act with
                    | inl _ => None
                    | inr act' => Some act'
                    end).

    Definition SendMediator_Channel_ReceiveMediator :=
      compose
        SendMediator_Channel
        ReorderingReceiveMediator
        (ChannelSenderAPI T + ChannelAPI (nat * T) + ChannelReceiverAPI T)
        (fun act => match act with
                    | inl act' => Some act'
                    | inr _ => None
                    end)
        (fun act => match act with
                    | inl act' => match act' with
                                  | inl _ => None
                                  | inr act'' => match act'' with
                                                 | inl _ => None
                                                 | inr act''' => Some (inl act''')
                                                 end
                                  end
                    | inr act' => Some (inr act')
                    end).

    Definition MediatedReliableReordering : AutomatonDef (ChannelAPI T) :=
      rename
        SendMediator_Channel_ReceiveMediator
        (ChannelAPI T)
        (fun act => match act with
                    | inl act' => inl (inl act')
                    | inr act' => inr act'
                    end)
        (ChannelAPI (nat * T))
        (fun act => inl (inr act)).

  End ReorderingMediator.

  Goal in_traces
       (MediatedReliableReordering _)
       [inl (Send 4); inl (Send 7); inr (Recv 4); inr (Recv 7)].
  Proof with ebreak_prod; simpl; intuition; auto.
    unfold in_traces.
    eexists; ebreak_compstate.
    exists_lift; [simpl; cbv; eauto|].
    eexists.
    estep_ext_break...
    estep_ext_break...
    (* let's have the mediator send in the "right" order *)
    estep_int_break (inr (inl (Send (0, _))))...
    estep_int_break (inr (inl (Send (1, _))))...
    (* let's have the channel send in the "wrong" order *)
    estep_int_break (inr (inr (Recv (1, _))))...
    apply removed_inside; apply removed_here.
    estep_int_break (inr (inr (Recv (0, _))))...
    estep_ext_break...
    estep_ext_break...
  Qed.

  Section ReorderingMediatorCorrect.

    Variable T : Type.

    (* [low, high) *)
    Inductive is_range : nat -> nat -> list (nat * T) -> Prop :=
    | is_range_empty : forall num,
        is_range num num []
    | is_range_step : forall low high t xs,
        is_range (S low) high xs ->
        is_range low high ((low, t) :: xs).

    Hint Constructors is_range.

    Lemma is_range_extend :
      forall low high xs t,
        is_range low high xs ->
        is_range low (S high) (xs ++ [(high, t)]).
    Proof.
      induction 1; simpl; auto.
    Qed.

    Lemma is_range_not_contains :
      forall low high xs n x,
        is_range low high xs ->
        n < low ->
        contains (n, x) xs ->
        False.
    Proof.
      intros low high xs n x Hrange.
      generalize dependent n.
      induction Hrange.
      - intros n Hlt Hct.
        inversion Hct.
      - intros n Hlt Hct.
        inversion Hct; intuition; subst; eauto.
        lia.
    Qed.

    Lemma is_range_contains :
      forall low high xs n t t',
        contains (n, t) ((n, t') :: xs) ->
        is_range low high ((n, t') :: xs) ->
        t = t'.
    Proof.
      intros low high xs n t t' Hct Hrange.
      destruct xs.
      - inversion Hct as [| p xs H].
        + auto.
        + inversion H.
      - inv_clear Hct.
        + auto.
        + exfalso.
          inversion Hrange as [|? ? ? ? Hrange']; clear Hrange.
          subst.
          clear t'.
          eapply is_range_not_contains; eauto.
    Qed.

    Theorem reordering_mediator_correct :
      refines (MediatedReliableReordering T) (Reliable T).
    Proof.
      apply forward_simulation with
      (f := fun st_impl st_spec =>
              let s := fst (fst st_impl) in
              let r := snd st_impl in
              let chan := snd (fst st_impl) in
              let union := snd s ++ chan ++ snd r in
              exists msgs,
                Permutation msgs union /\
                is_range (fst r) (fst s) msgs /\
                map snd msgs = st_spec).
      split.
      - intros s1 Hstart.
        destruct_compstate.
        repeat match goal with
               | [ H : start _ _ |- _ ] => inversion H; clear H
               end.
        simpl in *; subst.
        eexists; intuition.
        eexists; simpl; intuition.
      - intros s1' s1 act1 s2' Hstep Hrel.
        destruct act1 as [? | ?];
          repeat match goal with
                 | [ act : InternalActionType _ |- _ ] => destruct act
                 | [ act : ChannelAPI _ |- _ ] => destruct act
                 | [ act : ChannelSenderAPI _ |- _ ] => destruct act
                 | [ act : ChannelReceiverAPI _ |- _ ] => destruct act
                 | [ x : nat * T |- _ ] => destruct x
                 end;
          destruct Hrel as [msgs [Hsame [Hsorted Hmap]]].
        + eexists; simpl; split; [| apply Step_None; auto].
          exists msgs; intuition.
          simpl in Hstep; explode.
          eapply Permutation_trans; [apply Hsame |].
          do 2 rewrite app_assoc.
          apply Permutation_app.
          * destruct_compstate; simpl in *; destruct_prod;
              simpl in *; explode; subst.
            match goal with
            | [ |- Permutation (?a ++ ?x) (?b ++ ?x ++ [?c]) ] =>
              apply perm_trans with (x ++ [c] ++ b)
            end.
            -- eapply perm_trans.
               ++ apply Permutation_app_comm.
               ++ apply Permutation_app_head.
                  simpl.
                  apply removed_perm; auto.
            -- match goal with
               | [ |- Permutation (?a ++ ?b ++ ?c) (?c ++ ?a ++ ?b) ] =>
                 apply perm_trans with (a ++ c ++ b)
               end.
               ++ apply Permutation_app_head. apply Permutation_app_comm.
               ++ do 2 rewrite app_assoc.
                  apply Permutation_app_tail.
                  apply Permutation_app_comm.
          * destruct_compstate; simpl in *; subst; auto.
          * simpl in Hstep.
            destruct_compstate; simpl in *.
            destruct_prod; simpl in *.
            explode.
            subst; auto.
        + eexists; simpl; split; [| apply Step_None; auto].
          exists msgs; intuition.
          simpl in Hstep; explode.
          eapply Permutation_trans; [apply Hsame |].
          apply Permutation_app.
          * destruct_compstate; simpl in *; subst; auto.
          * destruct_compstate; simpl in *; destruct_prod;
              simpl in *; explode; subst.
            match goal with
            | [ |- Permutation (?a ++ ?x) (?b ++ ?x ++ [?c]) ] =>
              apply perm_trans with (x ++ [c] ++ b)
            end.
            -- eapply perm_trans.
               ++ apply Permutation_app_comm.
               ++ apply Permutation_app_head.
                  simpl.
                  apply removed_perm; auto.
            -- match goal with
               | [ |- Permutation (?a ++ ?b ++ ?c) (?c ++ ?a ++ ?b) ] =>
                 apply perm_trans with (a ++ c ++ b)
               end.
               ++ apply Permutation_app_head. apply Permutation_app_comm.
               ++ do 2 rewrite app_assoc.
                  apply Permutation_app_tail.
                  apply Permutation_app_comm.
          * simpl in Hstep.
            destruct_compstate; simpl in *.
            destruct_prod; simpl in *.
            explode.
            subst; auto.
        + eexists; simpl; split; [| estep_ext_break; simpl; intuition; auto].
          exists (msgs ++ [(fst (fst (fst s1')), t)]).
          split; [| split].
          * destruct_compstate; simpl in *; explode; subst.
            simpl.
            eapply perm_trans; [apply Permutation_app_comm |].
            match goal with
            | [ |- Permutation (?x ++ ?a) ((?b ++ ?x) ++ ?c ++ ?d) ] =>
              apply perm_trans with (x ++ b ++ c ++ d)
            end.
            -- apply Permutation_app_head; auto.
            -- repeat rewrite app_assoc.
               repeat apply Permutation_app_tail.
               apply Permutation_app_comm.
          * destruct_compstate; simpl in *.
            destruct_prod; simpl in *.
            explode; subst.
            rewrite plus_1_r.
            apply is_range_extend; auto.
          * rewrite map_app; rewrite Hmap; intuition.
        + destruct msgs as [| curr msgs'].
          * (* absurd case, can't be empty *)
            exfalso.
            destruct_compstate; simpl in *.
            destruct_prod; simpl in *.
            explode; subst.
            apply Permutation_nil in Hsame.
            repeat match goal with
                   | [ H : _ ++ _ = [] |- _ ] => symmetry in H
                   | [ H : _ |- _ ] => apply nil_eq_app in H; explode
                   end.
            subst.
            match goal with
            | [ H : removed _ [] _ |- _ ] => inversion H
            end.
          * destruct curr as [curr_n curr_m].
            (* need to prove that curr_m = t *)
            simpl in Hstep; explode.
            simpl in Hmap.
            simpl in Hsorted.
            inversion Hsorted; subst.
            assert (t = curr_m).
            -- eapply is_range_contains; [| apply Hsorted].
               apply Permutation_sym in Hsame.
               rewrite app_assoc in Hsame.
               eapply perm_trans in Hsame; [| solve [apply Permutation_app_comm]].
               match goal with
               | [ H : removed _ _ _ |- _ ] =>
                 apply removed_contains in H;
                   eapply contains_app in H;
                   eapply contains_perm in H
               end; eauto.
            -- subst.
               eexists; split; [| estep_ext_break; simpl; intuition; auto].
               exists msgs'.
               split; [| split].
               ++ destruct_compstate; simpl in *; subst; cleanup; subst.
                  apply Permutation_sym in Hsame.
                  rewrite app_assoc in Hsame.
                  eapply perm_trans in Hsame; [| solve [apply Permutation_app_comm]].
                  eapply perm_trans in Hsame;
                    [| solve [
                           apply Permutation_app_tail;
                           match goal with
                           | [ H : removed _ _ _ |- _ ] => apply removed_perm in H;
                                                           apply Permutation_sym in H;
                                                           apply H
                           end
                    ]].
                  simpl in Hsame.
                  apply Permutation_cons_inv in Hsame.
                  apply Permutation_sym.
                  eapply perm_trans; [| apply Hsame].
                  rewrite app_assoc.
                  apply Permutation_app_comm.
               ++ destruct_compstate; simpl in *; destruct_prod; simpl in *.
                  explode; subst.
                  rewrite plus_1_r; auto.
               ++ auto.
    Qed.

  End ReorderingMediatorCorrect.

End Channel.
