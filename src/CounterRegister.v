Require Import IOA.
Require Import CounterSpec.
Require Import Automation.
Require Import Simulation.
Require Import Misc.

Require Import List.
Import ListNotations.

Module CounterRegister.

  Import CounterSpec.Api.

  (* counter built on top of register *)

  Inductive Register_API :=
  | Reg_Set (value : nat)
  | Reg_Set_Done
  | Reg_Get_Request
  | Reg_Get_Response (value : nat).

  Inductive Register_pc := Reg_Ready | Reg_Setting | Reg_Getting.

  Definition Register_state : Set := Register_pc * nat.

  Definition Register_transition (st : Register_state) (act : EmptySet + Register_API) (st' : Register_state) : Prop :=
    match act with
    | inr (Reg_Set n) => (fst st = Reg_Ready /\ st' = (Reg_Setting, n)) \/
                         (fst st <> Reg_Ready /\ st' = st)
    | inr Reg_Set_Done => fst st = Reg_Setting /\ st' = (Reg_Ready, snd st)
    | inr Reg_Get_Request => (fst st = Reg_Ready /\ st' = (Reg_Getting, snd st)) \/
                             (fst st <> Reg_Ready /\ st' = st)
    | inr (Reg_Get_Response n) => st = (Reg_Getting, n) /\ st' = (Reg_Ready, n)
    | inl f => match f with end
    end.

  Definition Register_init value := value = (Reg_Ready, 0).

  Definition Register := mkAutomatonDef
                           Register_API
                           Register_state
                           _
                           Register_init
                           Register_transition.

  Example reg_trace1 : list Register_API :=
    [
      Reg_Get_Request;
        Reg_Get_Response 0;
        Reg_Set 3;
        Reg_Set_Done;
        Reg_Get_Request
    ].

  Example reg_trace1_valid : in_traces Register reg_trace1.
  Proof.
    eexists; eexists; split;
      [ cbv; eauto |
        repeat (eapply Step_External; simpl; eauto); econstructor; eauto ].
  Qed.

  Definition Counter_action_type : Set := Counter_API + Register_API.

  (* pc, cache *)

  Inductive DCounter_pc :=
  | DReady
  | DResetting1
  | DResetting2
  | DResetting3
  | DIncrementing1
  | DIncrementing2
  | DIncrementing3
  | DIncrementing4
  | DIncrementing5
  | DReading1
  | DReading2
  | DReading3.

  Definition Counter_state : Set := DCounter_pc * nat.

  Definition Counter_transition (st : Counter_state) (act : EmptySet + Counter_action_type) (st' : Counter_state) : Prop :=
    match act with
    | inr (inl Reset) => (fst st = DReady /\ st' = (DResetting1, snd st)) \/
                         (fst st <> DReady /\ st' = st)
    | inr (inr (Reg_Set n)) => match (fst st) with
                               | DResetting1 => n = 0 /\ st' = (DResetting2, snd st)
                               | DIncrementing3 => n = snd st /\ st' = (DIncrementing4, snd st)
                               | _ => False
                               end
    | inr (inr Reg_Set_Done) => match (fst st) with
                                | DResetting2 => st' = (DResetting3, snd st)
                                | DIncrementing4 => st' = (DIncrementing5, snd st)
                                | _ => st' = st
                                end
    | inr (inl Reset_Done) => fst st = DResetting3 /\ st' = (DReady, snd st)
    | inr (inl Increment) => (fst st = DReady /\ st' = (DIncrementing1, snd st)) \/
                             (fst st <> DReady /\ st' = st)
    | inr (inr Reg_Get_Request) => match (fst st) with
                                   | DIncrementing1 => st' = (DIncrementing2, snd st)
                                   | DReading1 => st' = (DReading2, snd st)
                                   | _ => False
                                   end
    | inr (inr (Reg_Get_Response n)) => match (fst st) with
                                        | DIncrementing2 => st' = (DIncrementing3, S n)
                                        | DReading2 => st' = (DReading3, n)
                                        | _ => st' = st
                                        end
    | inr (inl Increment_Done) => fst st = DIncrementing5 /\ st' = (DReady, snd st)
    | inr (inl Read_Request) => (fst st = DReady /\ st' = (DReading1, snd st)) \/
                                (fst st <> DReady /\ st' = st)
    | inr (inl (Read_Response n)) => st = (DReading3, n) /\ st' = (DReady, n)
    | inl f => match f with end
    end.

  Definition Counter_init st := st = (DReady, 0).

  Definition Counter : AutomatonDef Counter_action_type :=
    mkAutomatonDef
      _
      Counter_state
      _
      Counter_init
      Counter_transition.

  (* composition *)

  Definition Counter_Register_System : AutomatonDef (Counter_API + Register_API) :=
    compose
      Counter
      Register
      (Counter_API + Register_API)
      (fun act => Some act)
      (fun act => match act with
                  | inr reg_act => Some reg_act
                  | _ => None
                  end).
  Example counter_register_trace1 : list (Counter_API + Register_API) :=
    [
      inl Reset;
        inr (Reg_Set 0);
        inr Reg_Set_Done;
        inl Reset_Done
    ].

  Example counter_register_trace1_valid : in_traces Counter_Register_System counter_register_trace1.
  Proof.
    unfold in_traces; do 2 eexists; ebreak_compstate; split; [cbv; eauto |].
    repeat (estep_ext_break; simpl; eauto).
  Qed.

  Definition Counter_Register_System_external : AutomatonDef Counter_API :=
    rename
      Counter_Register_System
      Counter_API
      (fun act_counter => (inl act_counter))
      Register_API
      (fun act_reg => (inr act_reg)).

  Theorem counter_register_system_correct :
    refines
      Counter_Register_System_external
      Blocking.Spec.
  Proof.
    eapply forward_simulation with
    (f := (
           fun
             (st_impl : StateType Counter_Register_System_external)
             (st_spec : StateType Blocking.Spec) =>
             let ctr_pc := fst (fst st_impl) in
             let reg_pc := fst (snd st_impl) in
             let reg_value := snd (snd st_impl) in
             let ctr_cache := snd (fst st_impl) in
             let spec_pc := fst st_spec in
             let spec_value := snd st_spec in
             match ctr_pc with
             | DReady => reg_pc = Reg_Ready /\
                         spec_pc = Blocking.Ready /\
                         spec_value = reg_value
             | DResetting1 => reg_pc = Reg_Ready /\
                              spec_pc = Blocking.Resetting
             | DResetting2 => reg_pc = Reg_Setting /\
                              spec_pc = Blocking.Resetting /\
                              reg_value = 0
             | DResetting3 => reg_pc = Reg_Ready /\
                              spec_pc = Blocking.Resetting /\
                              reg_value = 0
             | DIncrementing1 => reg_pc = Reg_Ready /\
                                 spec_pc = Blocking.Incrementing /\
                                 spec_value = reg_value
             | DIncrementing2 => reg_pc = Reg_Getting /\
                                 spec_pc = Blocking.Incrementing /\
                                 spec_value = reg_value
             | DIncrementing3 => reg_pc = Reg_Ready /\
                                 spec_pc = Blocking.Incrementing /\
                                 spec_value = reg_value /\
                                 ctr_cache = S reg_value
             | DIncrementing4 => reg_pc = Reg_Setting /\
                                 spec_pc = Blocking.Incrementing /\
                                 S spec_value = reg_value
             | DIncrementing5 => reg_pc = Reg_Ready /\
                                 spec_pc = Blocking.Incrementing /\
                                 S spec_value = reg_value
             | DReading1 => reg_pc = Reg_Ready /\
                            spec_pc = Blocking.Reading /\
                            spec_value = reg_value
             | DReading2 => reg_pc = Reg_Getting /\
                            spec_pc = Blocking.Reading /\
                            spec_value = reg_value
             | DReading3 => reg_pc = Reg_Ready /\
                            spec_pc = Blocking.Reading /\
                            spec_value = reg_value /\
                            ctr_cache = reg_value
             end
         )
    ).
    split.
    - intros s1 Hstart.
      destruct s1 as [[ic_pc ic_v] [ir_pc ir_v]].
      inversion Hstart as [Hc Hr].
      inversion Hc; inversion Hr; subst.
      eexists; cbv; eauto.
    - intros s1' s1 act1 s2' Hstep Hrel.
      simpl in Hstep; unfold Rename_transition in Hstep.
      destruct act1 as [[iact | ract] | cact];
        [destruct iact as [icact | iract]; [destruct icact | destruct iract]
        | destruct ract | destruct cact];
        destruct s1' as [[s1'_cpc s1'_cv] [s1'_rpc s1'_rv]];
        destruct s1 as [[s1_cpc s1_cv] [s1_rpc s1_rv]];
        destruct s1_cpc;
        destruct s1'_cpc;
        subst;
        simpl in *;
        try (repeat break_or);
        shallow;
        abstract (
            destruct s2'; eexists; simpl in *; split; [
              explode; subst; intuition |
              econstructor; eauto; econstructor; intuition; explode
            ];
            subst;
            shallow
          ).
  Qed.

End CounterRegister.
