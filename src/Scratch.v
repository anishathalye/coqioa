Require Import IOA.
Require Import Misc.
Require Import ListOps.
Require Import OptionOps.
Require Import Simulation.
Require Import Automation.
Require Import Channel.

Require Import List.
Require Import Permutation.

Import ListNotations.

Module FlipFlop.

  Inductive FlipFlopAPI := toggle.
  Definition FlipFlop : AutomatonDef FlipFlopAPI :=
    mkAutomatonDef
      FlipFlopAPI
      bool
      EmptySet
      (fun st => True)
      (fun st act st' =>
         match act with
         | inl e => match e with end
         | inr toggle => match st with
                         | false => st' = true
                         | true => st' = false
                         end
         end).

  Definition FlipFlopFalse := parameterize FlipFlop (fun st => st = false).
  Definition FlipFlopTrue := parameterize FlipFlop (fun st => st = true).

  Definition FlipFlopPair : AutomatonDef FlipFlopAPI :=
    compose
      FlipFlopTrue
      FlipFlopFalse
      FlipFlopAPI
      Some
      Some.

  Lemma FlipFlop_opposite :
    invariant
      FlipFlopPair
      (fun st => fst st <> snd st).
  Proof.
    invariant_ind.
    - intros st Hstart.
      inversion Hstart as [[HT] [HF]].
      congruence.
    - intros st st' act P Hstep.
      destruct act as [[[] | []] | []].
      destruct st as [[] []]; simpl in *; intuition; congruence.
  Qed.

End FlipFlop.

(* from Computer-Assisted Simulation Proofs by Sogaard-Andersen,
Garland, Guttag, Lynch, and Pogosyants *)

Module LossyQueue.

  Section Main.

    Variable M : Type.
    Inductive Queue_API :=
    | Insert : M -> Queue_API
    | Remove : M -> Queue_API
    | Crash : Queue_API
    .
    Definition LossyQueue : AutomatonDef Queue_API :=
      mkAutomatonDef
        Queue_API
        (list M)
        EmptySet
        (fun st => st = [])
        (fun st act st' =>
           match act with
           | inl e => match e with end
           | inr Crash => subsequence st st'
           | inr (Insert m) => st' = st ++ [m]
           | inr (Remove m) => hd_error st = Some m /\ st' = tl st
           end).

    (* delayed implementation *)
    Inductive DQueue_internal := Lose.
    Definition DQueue : AutomatonDef Queue_API :=
      mkAutomatonDef
        Queue_API
        (list (M * bool))
        DQueue_internal
        (fun st => st = [])
        (fun st act st' =>
           match act with
           | inl Lose => subsequence_pred (fun x => snd x = true) st st'
           | inr Crash => st' = map (fun x => (fst x, true)) st
           | inr (Insert m) => st' = st ++ [(m, false)]
           | inr (Remove m) => option_map fst (hd_error st) = Some m /\ st' = tl st
           end).

    Theorem LossyQueue_impl_DQueue : refines LossyQueue DQueue.
    Proof.
      apply forward_simulation with
      (fun st_l st_d => map fst st_d = st_l).
      split.
      - intros s1 Hs1.
        inversion Hs1; subst.
        exists []; simpl; intuition.
      - intros s1' s1 act s2'.
        destruct act as [[] | []];
          intros Hstep Hrel.
        + (* insert *)
          inv_clear Hstep.
          exists (s2' ++ [(m, false)]).
          split.
          * rewrite map_app; subst; auto.
          * eapply Step_External; simpl; auto.
        + (* remove *)
          inv_clear Hstep.
          exists (tl s2').
          split.
          * subst. induction s2'; auto.
          * eapply Step_External; simpl; intuition.
            subst; induction s2'; auto.
        + (* crash - can be simulated by crash and lose (drop corresponding) *)
          exists (map (fun m => (m, true)) s1).
          split.
          * clear; induction s1; simpl; congruence.
          * simpl in Hstep.
            apply Step_External with (map (fun m => (m, true)) s1').
            -- subst; simpl.
               clear.
               rewrite list_map_map.
               induction s2'; simpl; auto.
            -- eapply Step_Internal with (int := Lose); eauto.
               simpl.
               clear Hrel.
               induction Hstep; simpl; auto.
    Qed.

  End Main.

End LossyQueue.

(*
two automata with one one-way channel in each direction (a total of 4
automata)
 *)

Module Ping.

  Import Channel.Channel.

  Inductive Ping_API := Ping | Ping_Done.
  Inductive A_PC := A_Ready | A_Sending | A_Sent | A_Received.
  Inductive B_PC := B_Ready | B_Busy.

  Definition A : AutomatonDef (Ping_API + ChannelSenderAPI unit + ChannelReceiverAPI unit) :=
    mkAutomatonDef
      _
      A_PC
      EmptySet
      (fun st => st = A_Ready)
      (fun st act st' =>
         match act with
         | inl e => match e with end
         | inr (inl (inl Ping)) => st' = A_Sending
         | inr (inl (inr (Send tt))) => st = A_Sending /\ st' = A_Sent
         | inr (inr (Recv tt)) => st' = A_Received
         | inr (inl (inl Ping_Done)) => st = A_Received /\ st' = A_Ready
         end).

  Definition B : AutomatonDef (ChannelSenderAPI unit + ChannelReceiverAPI unit) :=
    mkAutomatonDef
      _
      B_PC
      EmptySet
      (fun st => st = B_Ready)
      (fun st act st' =>
         match act with
         | inl e => match e with end
         | inr (inr (Recv tt)) => st' = B_Busy
         | inr (inl (Send tt)) => st = B_Busy /\ st' = B_Ready
         end).

  Definition A_sender : AutomatonDef _ :=
    compose
      A
      (Channel.Reliable unit)
      (* ping api, A's send channel, A's receive channel *)
      (Ping_API + (ChannelAPI unit) + ChannelReceiverAPI unit)
      (fun act => match act with
                  | inl (inl act') => Some (inl (inl act'))
                  | inl (inr (inl act')) => Some (inl (inr act'))
                  | inr act' => Some (inr act')
                  | _ => None
                  end)
      (fun act => match act with
                  | inl (inr act') => Some act'
                  | _ => None
                  end).

  Definition B_sender : AutomatonDef _ :=
    compose
      B
      (Channel.Reliable unit)
      (* B's receive channel, B's send channel *)
      (ChannelReceiverAPI unit + ChannelAPI unit)
      (fun act => match act with
                  | inl act' => Some (inr act')
                  | inr (inl act') => Some (inl act')
                  | _ => None
                  end)
      (fun act => match act with
                  | inr act' => Some act'
                  | _ => None
                  end).

  Definition AB_system_all : AutomatonDef _ :=
    compose
      A_sender
      B_sender
      (* ping api, A's send channel, B's send channel *)
      (Ping_API + ChannelAPI unit + ChannelAPI unit)
      (fun act => match act with
                  | inl act' => Some (inl act')
                  | inr (inr act') => Some (inr act')
                  | _ => None
                  end)
      (fun act => match act with
                  | inl (inr (inr act')) => Some (inl act')
                  | inr act' => Some (inr act')
                  | _ => None
                  end).

  Definition AB_system : AutomatonDef Ping_API :=
    rename
      AB_system_all
      Ping_API
      (fun act => inl (inl act))
      (ChannelAPI unit + ChannelAPI unit)
      (fun act => match act with
                  | inl act' => inl (inr act')
                  | inr act' => inr act'
                  end).

  Goal in_traces AB_system [Ping; Ping_Done].
  Proof with simpl; intuition; eauto.
    unfold in_traces.
    eexists; ebreak_compstate.
    exists_lift; [simpl; cbv; eauto|].
    eexists.
    estep_ext_break...
    estep_int_break (inr (inl (inl (Send tt))))...
    estep_int_break (inr (inl (inr (Recv tt))))...
    estep_int_break (inr (inr (inl (Send tt))))...
    estep_int_break (inr (inr (inr (Recv tt))))...
    estep_ext_break...
  Qed.

End Ping.

(* Butler Lampson, Reliable Messages and Connection Establishment *)

Module ReliableMessaging.

  Section Main.

    Variable M : Type.
    Variable I : Type.
    Variable I_eq_dec : forall (i i' : I), {i = i'} + {i <> i'}.

    (* Spec *)

    Inductive A := A_ok | A_lost.
    Inductive Status := S_ok | S_lost | S_unknown.
    Definition status_eq_a (status : Status) (a : A) : Prop :=
      (status = S_ok /\ a = A_ok) \/ (status = S_lost /\ a = A_lost).
    Record Spec_state := mkSpecState {
                             q : list M;
                             status : Status;
                             rec_s : bool;
                             rec_r : bool
                           }.
    Definition Spec_start (st : Spec_state) : Prop :=
      st = mkSpecState [] S_lost false false.
    Inductive Action :=
    | put : M -> Action
    | getAck : A -> Action
    | get : M -> Action
    | crash_s : Action
    | recover_s : Action
    | crash_r : Action
    | recover_r : Action
    .
    Inductive Spec_internal := lose.
    Definition Spec_transition
               (st : Spec_state) (act : Spec_internal + Action) (st' : Spec_state) : Prop :=
      match act with
      | inl int =>
        match int with
        | lose => (st.(rec_s) = true \/ st.(rec_r) = true) /\
                  ((exists q', one_removed st.(q) q' /\
                               st' = mkSpecState q' (match q' with
                                                     | [] => S_lost
                                                     | _ => st.(status)
                                                     end) st.(rec_s) st.(rec_r)) \/
                   (st' = mkSpecState st.(q) S_lost st.(rec_s) st.(rec_r)))
        end
      | inr ext =>
        match ext with
        | put m => st.(rec_s) = false /\
                   st' = mkSpecState (st.(q) ++ [m]) S_unknown st.(rec_s) st.(rec_r)
        | getAck a => st.(rec_s) = false /\ status_eq_a st.(status) a /\
                      (st' = st \/
                       st' = mkSpecState st.(q) S_lost st.(rec_s) st.(rec_r))
        | get m => st.(rec_r) = false /\ hd_error st.(q) = Some m /\
                   st' = mkSpecState (tl st.(q)) (match (tl st.(q)) with
                                                  | [] => match st.(status) with
                                                          | S_unknown => S_ok
                                                          | _ => st.(status)
                                                          end
                                                  | _ => st.(status)
                                                  end) st.(rec_s) st.(rec_r)
        | crash_s => st' = mkSpecState st.(q) st.(status) true st.(rec_r)
        | recover_s => st.(rec_s) = true /\
                       st' = mkSpecState st.(q) st.(status) false st.(rec_r)
        | crash_r => st' = mkSpecState st.(q) st.(status) st.(rec_s) true
        | recover_r => st.(rec_r) = true /\
                       st' = mkSpecState st.(q) st.(status) st.(rec_s) false
        end
      end.
    Definition Spec : AutomatonDef Action :=
      mkAutomatonDef _ Spec_state _ Spec_start Spec_transition.

    (* Delayed-Decision Spec *)
    (* mark "+" corresponds to true, mark "#" corresponds to false *)
    Record DSpec_state := mkDSpecState {
                              dq : list (M * bool);
                              dstatus : Status * bool;
                              drec_s : bool;
                              drec_r : bool;
                            }.
    Definition DSpec_start (st : DSpec_state) : Prop :=
      st = mkDSpecState [] (S_lost, true) false false.
    Inductive DSpec_internal := mark | drop | unmark.
    Definition DSpec_transition
               (st : DSpec_state) (act : DSpec_internal + Action) (st' : DSpec_state) : Prop :=
      match act with
      | inl int =>
        match int with
        | mark => (st.(drec_s) = true \/ st.(drec_r) = true) /\
                  ((exists q', one_changed (fun e => (fst e, false)) st.(dq) q' /\
                               st' = mkDSpecState q' st.(dstatus) st.(drec_s) st.(drec_r)) \/
                   (st' = mkDSpecState st.(dq) (fst st.(dstatus), false) st.(drec_s) st.(drec_r)))
        | unmark => (st.(drec_s) = true \/ st.(drec_r) = true) /\
                    ((exists q', one_changed (fun e => (fst e, true)) st.(dq) q' /\
                                 st' = mkDSpecState q' st.(dstatus) st.(drec_s) st.(drec_r)) \/
                     (st' = mkDSpecState st.(dq) (fst st.(dstatus), true) st.(drec_s) st.(drec_r)))
        | drop => (exists q', one_removed_pred (fun e => snd e = false) st.(dq) q' /\
                              st' = mkDSpecState q' (match q' with
                                                     | [] => (S_lost, true)
                                                     | _ => st.(dstatus)
                                                     end) st.(drec_s) st.(drec_r)) \/
                  (snd st.(dstatus) = false /\
                   st' = mkDSpecState st.(dq) (S_lost, true) st.(drec_s) st.(drec_r))
        end
      | inr ext =>
        match ext with
        | put m => st.(drec_s) = false /\
                   st' = mkDSpecState (st.(dq) ++ [(m, true)]) (S_unknown, true) st.(drec_s) st.(drec_r)
        | getAck a => st.(drec_s) = false /\ status_eq_a (fst st.(dstatus)) a /\
                      (st' = mkDSpecState st.(dq) (fst st.(dstatus), true) st.(drec_s) st.(drec_r) \/
                       st' = mkDSpecState st.(dq) (S_lost, true) st.(drec_s) st.(drec_r))
        | get m => st.(drec_r) = false /\ option_map fst (hd_error st.(dq)) = Some m /\
                   st' = mkDSpecState (tl st.(dq)) (match (tl st.(dq)) with
                                                    | [] => match st.(dstatus) with
                                                            | (S_unknown, x) => (S_ok, x)
                                                            | _ => st.(dstatus)
                                                            end
                                                    | _ => st.(dstatus)
                                                    end) st.(drec_s) st.(drec_r)
        | crash_s => st' = mkDSpecState st.(dq) st.(dstatus) true st.(drec_r)
        | recover_s => st.(drec_s) = true /\
                       st' = mkDSpecState st.(dq) st.(dstatus) false st.(drec_r)
        | crash_r => st' = mkDSpecState st.(dq) st.(dstatus) st.(drec_s) true
        | recover_r => st.(drec_r) = true /\
                       st' = mkDSpecState st.(dq) st.(dstatus) st.(drec_s) false
        end
      end.
    Definition DSpec : AutomatonDef Action :=
      mkAutomatonDef _ DSpec_state _ DSpec_start DSpec_transition.

  End Main.

End ReliableMessaging.

Module CounterClock.

  Inductive ClockAPI := Tick.

  Definition Clock :=
    mkAutomatonDef ClockAPI unit EmptySet
      (fun _ => True) (fun _ _ _ => True). (* can tick at any time *)

  Inductive CounterAPI := Count : nat -> CounterAPI.

  Definition Counter :=
    mkAutomatonDef
      (CounterAPI + ClockAPI) nat EmptySet
      (fun st => st = 0)
      (fun st act st' =>
         match act with
         | inl e => match e with end
         | inr (inr Tick) => st' = st + 1
         | inr (inl (Count n)) => st = n /\ st' = st
         end).

  Definition CounterClock :=
    compose
      Counter
      Clock
      (CounterAPI + ClockAPI)
      (fun act => Some act)
      (fun act => match act with
                  | inl _ => None
                  | inr act' => Some act'
                  end).

End CounterClock.
