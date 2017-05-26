Require Import IOA.
Require Import Network.
Require Import Simulation.
Require Import CounterSpec.
Require Import CounterRegister.
Require Import Automation.
Require Import Misc.
Require Import ListOps.

Require Import List.
Import ListNotations.

Module CounterNetworked.

  Import CounterSpec.Api.
  Import CounterRegister.CounterRegister.

  (* counter built on top of register, but connected by
     network. basically a copy of CounterRegister, but uses Network *)

  Inductive Address := CounterAddr | RegisterAddr.

  Lemma Address_eq_dec : forall (a a' : Address),
      {a = a'} + {a <> a'}.
  Proof.
    decide equality.
  Defined.

  Definition Message := Register_API.

  Lemma Message_eq_dec : forall (m m' : Message),
      {m = m'} + {m <> m'}.
  Proof.
    repeat (decide equality).
  Defined.

  Definition CRNetwork : AutomatonDef (Network_API Address Message) :=
    Network _ _ Address_eq_dec Message_eq_dec.

  Definition Register_API_N : Type := Network_API Address Message.

  Definition CRNetwork_actions : Type := Network_actions Address Message.

  Definition Register_transition (st : Register_state) (act : Register_API_N) (st' : Register_state) : Prop :=
    match act with
    | Recv CounterAddr (Reg_Set n) RegisterAddr => (fst st = Reg_Ready /\ st' = (Reg_Setting, n)) \/
                                                   (fst st <> Reg_Ready /\ st' = st)
    | Send RegisterAddr Reg_Set_Done CounterAddr => fst st = Reg_Setting /\ st' = (Reg_Ready, snd st)
    | Recv CounterAddr Reg_Get_Request RegisterAddr => (fst st = Reg_Ready /\ st' = (Reg_Getting, snd st)) \/
                                                       (fst st <> Reg_Ready /\ st' = st)
    | Send RegisterAddr (Reg_Get_Response n) CounterAddr => st = (Reg_Getting, n) /\ st' = (Reg_Ready, n)
    | Send _ _ _ => False
    | Recv _ _ _ => st' = st (* input-enabled *)
    end.

  Definition Register : AutomatonDef Register_API_N :=
    mkAutomatonDef
      _
      Register_state
      EmptySet
      Register_init
      (liftExternal Register_transition).

  Goal in_traces Register
       [
         Recv CounterAddr Reg_Get_Request RegisterAddr;
           Send RegisterAddr (Reg_Get_Response 0) CounterAddr;
           Recv CounterAddr (Reg_Set 3) RegisterAddr;
           Send RegisterAddr Reg_Set_Done CounterAddr
       ].
  Proof.
    eexists ((_, _)); eexists ((_, _)); split; [hnf; eauto |].
    repeat (eapply Step_External; simpl; eauto).
  Qed.

  Definition Counter_action_type : Type := Counter_API + Register_API_N.

  Definition Counter_transition (st : Counter_state) (act : Counter_action_type) (st' : Counter_state) : Prop :=
    match act with
    | inl Reset => (fst st = DReady /\ st' = (DResetting1, snd st)) \/
                   (fst st <> DReady /\ st' = st)
    | inr (Send CounterAddr (Reg_Set n) RegisterAddr) =>
      match (fst st) with
      | DResetting1 => n = 0 /\ st' = (DResetting2, snd st)
      | DIncrementing3 => n = snd st /\ st' = (DIncrementing4, snd st)
      | _ => False
      end
    | inr (Recv RegisterAddr Reg_Set_Done CounterAddr) =>
      match (fst st) with
      | DResetting2 => st' = (DResetting3, snd st)
      | DIncrementing4 => st' = (DIncrementing5, snd st)
      | _ => st' = st
      end
    | inl Reset_Done => fst st = DResetting3 /\ st' = (DReady, snd st)
    | inl Increment => (fst st = DReady /\ st' = (DIncrementing1, snd st)) \/
                       (fst st <> DReady /\ st' = st)
    | inr (Send CounterAddr Reg_Get_Request RegisterAddr) =>
      match (fst st) with
      | DIncrementing1 => st' = (DIncrementing2, snd st)
      | DReading1 => st' = (DReading2, snd st)
      | _ => False
      end
    | inr (Recv RegisterAddr (Reg_Get_Response n) CounterAddr) =>
      match (fst st) with
      | DIncrementing2 => st' = (DIncrementing3, S n)
      | DReading2 => st' = (DReading3, n)
      | _ => st' = st
      end
    | inl Increment_Done => fst st = DIncrementing5 /\ st' = (DReady, snd st)
    | inl Read_Request => (fst st = DReady /\ st' = (DReading1, snd st)) \/
                          (fst st <> DReady /\ st' = st)
    | inl (Read_Response n) => st = (DReading3, n) /\ st' = (DReady, n)
    | inr (Recv _ _ _) => st' = st
    | inr (Send _ _ _) => False
    end.

  Definition Counter : AutomatonDef _ :=
    mkAutomatonDef
      _
      Counter_state
      EmptySet
      Counter_init
      (liftExternal Counter_transition).

  Definition Counter_Register : AutomatonDef (Counter_API + Register_API_N) :=
    compose
      Counter
      Register
      _
      (fun act => match act with
                  | inl act_ctr => Some act
                  | inr (Recv _ _ CounterAddr) => Some act
                  | inr (Send CounterAddr _ _) => Some act
                  | inr _ => None
                  end)
      (fun act => match act with
                  | inr act_net => match act_net with
                                   | Recv _ _ RegisterAddr => Some act_net
                                   | Send RegisterAddr _ _ => Some act_net
                                   | _ => None
                                   end
                  | _ => None
                  end).

  Definition Counter_Register_Networked : AutomatonDef (Counter_API + Register_API_N) :=
    compose
      Counter_Register
      CRNetwork
      (Counter_API + Network_API Address Message)
      (fun act => Some act)
      (fun act => match act with
                  | inr act_net => Some act_net
                  | _ => None
                  end).

  Definition Counter_Register_Networked_external : AutomatonDef Counter_API :=
    rename
      Counter_Register_Networked
      Counter_API
      (fun act_ctr => inl act_ctr)
      Register_API_N
      (fun act_reg => inr act_reg).

  Goal in_traces Counter_Register_Networked_external
       [
         Increment;
           Increment_Done
       ].
  Proof.
    (* a horrible, messy proof that should be automated *)
    unfold in_traces.
    eexists ((_, _), nil).
    eexists; split; [cbv; auto | ].
    estep_ext_break; [cbv; auto |].
    estep_int_break (inr (Send CounterAddr Reg_Get_Request RegisterAddr)); [cbv; eauto |].
    estep_int_break (inr (Recv CounterAddr Reg_Get_Request RegisterAddr));
      [simpl; intuition; destruct (Address_eq_dec _ _); destruct (Message_eq_dec); destruct (Address_eq_dec _ _); try congruence; intuition | ].
    estep_int_break (inr (Send RegisterAddr (Reg_Get_Response 0) CounterAddr)); [cbv; eauto |].
    estep_int_break (inr (Recv RegisterAddr (Reg_Get_Response 0) CounterAddr)); [cbv; eauto |].
    estep_int_break (inr (Send CounterAddr (Reg_Set 1) RegisterAddr)); [cbv; eauto |].
    estep_int_break (inr (Recv CounterAddr (Reg_Set 1) RegisterAddr));
      [simpl; intuition; destruct (Address_eq_dec _ _); destruct (Message_eq_dec); destruct (Address_eq_dec _ _); try congruence; intuition | ].
    estep_int_break (inr (Send RegisterAddr Reg_Set_Done CounterAddr)); [cbv; eauto |].
    estep_int_break (inr (Recv RegisterAddr Reg_Set_Done CounterAddr)); [cbv; eauto |].
    estep_ext_break; [cbv; auto |].
    eauto.
  Qed.

  Ltac in_single :=
    match goal with
    | [ H : In _ [?x] |- _ ] => inversion H; clear H; shallow
    end.

  Ltac packet_eq :=
    match goal with
    | [ H : mkPacket _ _ _ = mkPacket _ _ _ |- _ ] => inversion H; clear H; subst
    end.

  Theorem counter_register_networked_correct :
    refines Counter_Register_Networked_external CounterSpec.Blocking.Spec.
  Proof.
    apply refines_trans with (intermediate := Counter_Register_System_external); auto using counter_register_system_correct.
    apply forward_simulation with
    (f := fun
           (st_net : StateType Counter_Register_Networked_external)
           (st_dist : StateType Counter_Register_System_external) =>
           let pkts := snd st_net in
           let net_ctr := fst (fst st_net) in
           let net_reg := snd (fst st_net) in
           let net_ctr_pc := fst net_ctr in
           let net_ctr_val := snd net_ctr in
           let net_reg_pc := fst net_reg in
           let net_reg_val := snd net_reg in
           let dist_ctr := fst st_dist in
           let dist_reg := snd st_dist in
           let dist_ctr_pc := fst dist_ctr in
           let dist_ctr_val := snd dist_ctr in
           let dist_reg_pc := fst dist_reg in
           let dist_reg_val := snd dist_reg in

           (* this is probably too detailed reasoning about network state... *)
           match dist_ctr_pc with
           | DReady => net_ctr = dist_ctr /\ net_reg = dist_reg /\ dist_reg_pc = Reg_Ready /\ pkts = nil
           | DIncrementing1 => net_ctr = dist_ctr /\ net_reg = dist_reg /\ dist_reg_pc = Reg_Ready /\ pkts = nil
           | DIncrementing2 => net_ctr_pc = DIncrementing2 /\
                               dist_reg_pc = Reg_Getting /\
                               net_ctr_val = dist_ctr_val /\
                               net_reg_val = dist_reg_val /\
                               ((pkts = [mkPacket CounterAddr Reg_Get_Request RegisterAddr] /\ net_reg_pc = Reg_Ready) \/
                                (pkts = nil /\ net_reg_pc = Reg_Ready) \/
                                (pkts = nil /\ net_reg_pc = Reg_Getting) \/
                                (pkts = [mkPacket RegisterAddr (Reg_Get_Response net_reg_val) CounterAddr] /\ net_reg_pc = Reg_Ready))
           | DIncrementing3 => net_ctr = dist_ctr /\ net_reg = dist_reg /\ dist_reg_pc = Reg_Ready /\ pkts = nil
           | DIncrementing4 => net_ctr_pc = DIncrementing4 /\
                               dist_reg_pc = Reg_Setting /\
                               net_ctr_val = dist_ctr_val /\
                               dist_reg_val = dist_ctr_val /\
                               ((pkts = [mkPacket CounterAddr (Reg_Set net_ctr_val) RegisterAddr] /\ net_reg_pc = Reg_Ready) \/
                                (pkts = nil /\ net_reg_pc = Reg_Ready) \/
                                (pkts = nil /\ net_reg_pc = Reg_Setting /\ net_reg_val = net_ctr_val) \/
                                (pkts = [mkPacket RegisterAddr Reg_Set_Done CounterAddr] /\ net_reg_pc = Reg_Ready /\ net_reg_val = net_ctr_val) \/
                                (pkts = nil /\ net_reg_pc = Reg_Ready /\ net_reg_val = net_ctr_val))
           | DIncrementing5 => net_ctr = dist_ctr /\ net_reg = dist_reg /\ dist_reg_pc = Reg_Ready /\ pkts = nil
           | DResetting1 => net_ctr = dist_ctr /\ net_reg = dist_reg /\ dist_reg_pc = Reg_Ready /\ pkts = nil
           | DResetting2 => net_ctr_pc = DResetting2 /\
                            dist_reg_pc = Reg_Setting /\
                            net_ctr_val = dist_ctr_val /\
                            dist_reg_val = 0 /\
                            ((pkts = [mkPacket CounterAddr (Reg_Set 0) RegisterAddr] /\ net_reg_pc = Reg_Ready) \/
                             (pkts = nil /\ net_reg_pc = Reg_Ready) \/
                             (pkts = nil /\ net_reg_pc = Reg_Setting /\ net_reg_val = 0) \/
                             (pkts = [mkPacket RegisterAddr Reg_Set_Done CounterAddr] /\ net_reg_pc = Reg_Ready /\ net_reg_val = 0) \/
                             (pkts = nil /\ net_reg_pc = Reg_Ready /\ net_reg_val = 0))
           | DResetting3 => net_ctr = dist_ctr /\ net_reg = dist_reg /\ dist_reg_pc = Reg_Ready /\ pkts = nil
           | DReading1 => net_ctr = dist_ctr /\ net_reg = dist_reg /\ dist_reg_pc = Reg_Ready /\ pkts = nil
           | DReading2 => net_ctr_pc = DReading2 /\
                          dist_reg_pc = Reg_Getting /\
                          net_ctr_val = dist_ctr_val /\
                          net_reg_val = dist_reg_val /\
                          ((pkts = [mkPacket CounterAddr Reg_Get_Request RegisterAddr] /\ net_reg_pc = Reg_Ready) \/
                           (pkts = nil /\ net_reg_pc = Reg_Ready) \/
                           (pkts = nil /\ net_reg_pc = Reg_Getting) \/
                           (pkts = [mkPacket RegisterAddr (Reg_Get_Response net_reg_val) CounterAddr] /\ net_reg_pc = Reg_Ready))
           | DReading3 => net_ctr = dist_ctr /\ net_reg = dist_reg /\ dist_reg_pc = Reg_Ready /\ pkts = nil
           end
    ).
    split.
    - intros s1 Hstart.
      destruct s1 as [[[ic_pc ic_v] [ir_pc ir_v]] msgs].
      inversion Hstart as [[Hc Hr] Hn].
      inversion Hc; inversion Hr; inversion Hn; simpl in *.
      eexists; ebreak_compstate; cbv; intuition.
    - intros s1' s1 act1 s2' Hstep Hrel.
      simpl in Hstep; unfold Rename_transition in Hstep.
      destruct act1 as [[[[[] | []] | inact] | ract] | cact].
      + (* drop *)
        destruct inact.
        simpl in Hrel.
        destruct s1' as [[[s1'_cpc s1'_cv] [s1'_rpc s1'_rv]] s1'_msgs];
          destruct s1 as [[[s1_cpc s1_cv] [s1_rpc s1_rv]] s1_msgs];
          destruct s2' as [[s2'_cpc s2'_cv] [s2'_rpc s2'_rv]];
          simpl in *.
        destruct s2'_cpc eqn:H;
          try solve [inversion Hstep as [[? [Hx ?]] ?]; intuition; subst; inversion Hx];
          exists ((s2'_cpc, s2'_cv), (s2'_rpc, s2'_rv)).
        all:
          destruct Hrel;
          explode;
          subst;
          simpl;
          auto.
        all:
          split; [| solve [econstructor; eauto]];
          explode;
          subst;
          intuition;
          cleanup;
          subst;
          match goal with
          | [ H : In _ [] |- _ ] => solve [inversion H]
          | [ H : In _ _ |- _ ] => destruct H as [H | H]; [rewrite H | solve by inversion]
          end;
          eauto using remove_one_only.
      + (* send/recv *)
        destruct s1' as [[[s1'_cpc s1'_cv] [s1'_rpc s1'_rv]] s1'_msgs];
          destruct s1 as [[[s1_cpc s1_cv] [s1_rpc s1_rv]] s1_msgs];
          destruct s2' as [[s2'_cpc s2'_cv] [s2'_rpc s2'_rv]].
        destruct ract as [src m dst | src m dst].
        * (* send *)
          destruct src; destruct dst; destruct m; simpl in *; try solve [intuition].
          -- destruct s1'_cpc; destruct s1'_rpc; try tauto;
               destruct s2'_cpc; cleanup; try congruence.
             ++ eexists ((DResetting2, _), (_, _)).
                simpl; split.
                ** repeat split; subst; eauto.
                ** eapply Step_Internal with (int := inr (Reg_Set _)); [| eapply Step_None];
                     eauto; simpl; intuition.
             ++ eexists ((DIncrementing4, _), (_, _)).
                simpl; split.
                ** repeat split; subst; eauto.
                ** eapply Step_Internal with (int := inr (Reg_Set _)); [| eapply Step_None];
                     eauto; simpl; intuition.
          -- destruct s1'_cpc; destruct s1'_rpc; try tauto;
               destruct s2'_cpc; cleanup; try congruence.
             ++ eexists ((DIncrementing2, _), (_, _)).
                simpl; split.
                ** repeat split; subst; eauto.
                ** eapply Step_Internal with (int := inr (Reg_Get_Request)); [| eapply Step_None];
                     eauto; simpl; intuition.
             ++ eexists ((DReading2, _), (_, _)).
                simpl; split.
                ** repeat split; subst; eauto.
                ** eapply Step_Internal with (int := inr (Reg_Get_Request)); [| eapply Step_None];
                     eauto; simpl; intuition.
          -- destruct s1'_cpc; destruct s1'_rpc; try tauto;
               destruct s2'_cpc;
               cleanup;
               try congruence;
               repeat break_or;
               try solve [intuition; congruence];
               cleanup.
             ++ eexists ((DResetting2, _), (_, _)).
                simpl; split.
                ** repeat split; subst; eauto 10.
                ** subst; simpl; eauto.
             ++ eexists ((DIncrementing4, _), (_, _)).
                simpl; split.
                ** repeat split; subst; eauto 10.
                ** subst; simpl; eauto.
          -- destruct s1'_cpc; destruct s1'_rpc; try tauto;
               destruct s2'_cpc;
               cleanup;
               try congruence;
               repeat break_or;
               try solve [intuition; congruence];
               cleanup.
             ++ eexists ((DIncrementing2, _), (_, _)).
                simpl; split.
                ** repeat split; subst; eauto.
                ** subst; simpl; eauto.
             ++ eexists ((DReading2, _), (_, _)).
                simpl; split.
                ** repeat split; subst; eauto.
                ** subst; simpl; eauto.
        * (* recv *)
          destruct src; destruct dst; destruct m; simpl in *;
            try solve [exfalso; destruct s2'_cpc; cleanup; repeat break_or; cleanup; subst; shallow].
          -- destruct s2'_cpc; cleanup; repeat break_or; cleanup; subst; shallow.
             ++ in_single; packet_eq;
                  eexists ((DResetting2, _), (_, _)); split.
                ** repeat split; eauto 10.
                ** simpl; eauto.
             ++ in_single; packet_eq;
                  eexists ((DIncrementing4, _), (_, _)); split.
                ** repeat split; eauto 10 using remove_one_only.
                ** simpl; eauto.
          -- destruct s2'_cpc; cleanup; repeat break_or; cleanup; subst; shallow.
             ++ in_single; packet_eq.
                eexists ((DIncrementing2, _), (_, _)); split.
                ** repeat split; eauto 10.
                ** simpl; eauto.
             ++ in_single; packet_eq.
                eexists ((DReading2, _), (_, _)); split.
                ** repeat split; eauto 10.
                ** simpl; eauto.
          -- destruct s2'_cpc; cleanup; repeat break_or; cleanup; subst; shallow.
             ++ in_single; packet_eq.
                eexists ((DResetting3, _), (_, _)); split.
                ** repeat split; simpl; eauto 10.
                ** eapply Step_Internal with (int := inr (Reg_Set_Done)); [| eapply Step_None];
                     eauto; simpl; intuition.
             ++ in_single; packet_eq.
                eexists ((DIncrementing5, _), (_, _)); split.
                ** repeat split; simpl; eauto 10.
                ** eapply Step_Internal with (int := inr (Reg_Set_Done)); [| eapply Step_None];
                     eauto; simpl; intuition.
          -- destruct s2'_cpc; cleanup; repeat break_or; cleanup; subst; shallow.
             ++ in_single; packet_eq.
                eexists ((DIncrementing3, _), (_, _)); split.
                ** repeat split; eauto using remove_one_only; simpl; eauto.
                ** eapply Step_Internal with (int := inr (Reg_Get_Response _)); [| eapply Step_None];
                     eauto; simpl; intuition.
             ++ in_single; packet_eq.
                eexists ((DReading3, _), (_, _)); split.
                ** repeat split; eauto using remove_one_only; simpl; eauto.
                ** eapply Step_Internal with (int := inr (Reg_Get_Response _)); [| eapply Step_None];
                     eauto; simpl; intuition.
      + (* counter API *)
        destruct s1' as [[[s1'_cpc s1'_cv] [s1'_rpc s1'_rv]] s1'_msgs];
          destruct s1 as [[[s1_cpc s1_cv] [s1_rpc s1_rv]] s1_msgs];
          destruct s2' as [[s2'_cpc s2'_cv] [s2'_rpc s2'_rv]];
          simpl in *.
        eexists ((s1_cpc, s2'_cv), (s2'_rpc, s2'_rv)). (* identical, only thing that could change is counter pc *)
        destruct s1'_cpc eqn:Hc1cpc; destruct s2'_cpc eqn:Hs2cpc; try solve [exfalso; cleanup; congruence];
          destruct cact eqn:Hcact; cleanup; subst; cleanup; simpl in *; try congruence;
            try break_or; shallow; cleanup; subst; intuition;
              eapply Step_External; eauto; simpl; eauto.
  Qed.

End CounterNetworked.
