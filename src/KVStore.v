Require Import IOA.
Require Import Misc.
Require Import ListOps.
Require Import OptionOps.
Require Import Simulation.
Require Import RefinementFacts.
Require Import Automation.
Require Import Channel.

Require Import List.
Import ListNotations.
Require Import Peano_dec.
Require Import Arith.Even.

Inductive API :=
| Put (k : nat) (v : nat)
| PutOk
| Get (k : nat)
| GetResult (v : option nat).

Module Spec.

  Inductive Request :=
  | Req_Put (k : nat) (v : nat)
  | Req_Get (k : nat).
  Inductive Response :=
  | Resp_Ok
  | Resp_Value (v : option nat).
  Inductive Internal := Execute.

  Record state : Type := mkState {
                             requests : list Request;
                             responses : list Response;
                             data : nat -> option nat;
                           }.
  Definition start (st : state) : Prop := st = mkState [] [] (fun _ => None).

  Definition step (st : state) (act : Internal + API) (st' : state) : Prop :=
    let (req, res, d) := st in
    match act with
    | inr (Put k v) => st' = mkState (req ++ [Req_Put k v]) res d
    | inr (Get k) => st' = mkState (req ++ [Req_Get k]) res d
    | inl Execute =>
      exists hd tl, req = hd :: tl /\
                    st' = mkState tl
                                  (res ++ [match hd with
                                           | Req_Get k => Resp_Value (d k)
                                           | _ => Resp_Ok
                                           end])
                                  (match hd with
                                   | Req_Put k v =>
                                     fun k' => if eq_nat_dec k k' then
                                                 Some v else
                                                 d k'
                                   | _ => d
                                   end)
    | inr PutOk => exists tl, res = Resp_Ok :: tl /\ st' = mkState req tl d
    | inr (GetResult v) => exists tl, res = (Resp_Value v) :: tl /\ st' = mkState req tl d
    end.

  Definition KVStore : AutomatonDef API :=
    mkAutomatonDef API state Internal start step.

  Ltac break_state :=
    match goal with
    | [ |- context[ ?x ] ] =>
      is_evar x;
      let T := type of x in
      lazymatch eval simpl in T with
      | state =>
        let x1 := fresh "x" in
        let x2 := fresh "y" in
        let x3 := fresh "z" in
        evar (x1 : list Request);
        evar (x2 : list Response);
        evar (x3 : nat -> option nat);
        unify x (mkState x1 x2 x3);
        clear x1 x2 x3
      end
    end.

  Tactic Notation "ext" :=
    estep_ext_break; [solve [break_state; simpl; eauto] |].

  Tactic Notation "int" :=
    estep_int_break Execute; [
      solve [break_state; simpl; eauto] |].

  Goal in_traces KVStore [
         Put 3 4;
           Get 3;
           PutOk;
           GetResult (Some 4);
           Put 3 5;
           PutOk;
           Get 3;
           GetResult (Some 5);
           Get 4;
           GetResult None
       ].
  Proof.
    unfold in_traces.
    eexists; exists_lift; [cbv; eauto |].
    eexists.
    repeat (ext || int); eauto.
  Qed.

End Spec.

Module ClientServer.

  Section Main.

    Import Channel.
    Import Spec.

    Definition ServerAPI : Type :=
      (ChannelReceiverAPI Request) + (ChannelSenderAPI Response).

    Definition server_state : Type := (list Response) * (nat -> option nat).

    Definition server_start (st : server_state) : Prop :=
      st = ([], fun _ => None).

    Definition server_step (st : server_state) (act : EmptySet + ServerAPI) (st' : server_state) :=
      let (resp, m) := st in
      match act with
      | inl e => match e with end
      | inr (inl (Recv (Req_Put k v))) =>
        st' = (resp ++ [Resp_Ok], fun k' => if eq_nat_dec k k' then Some v else m k')
      | inr (inl (Recv (Req_Get k))) =>
        st' = (resp ++ [Resp_Value (m k)], m)
      | inr (inr (Send msg)) =>
        exists tl, resp = msg :: tl /\ st' = (tl, m)
      end.

    Definition Server : AutomatonDef ServerAPI :=
      mkAutomatonDef ServerAPI server_state EmptySet server_start server_step.

    Definition ClientAPI : Type :=
      API + (ChannelSenderAPI Request + ChannelReceiverAPI Response).

    Definition client_state : Type := (list Request * list Response).

    Definition client_start (st : client_state) := st = ([], []).

    Definition client_step (st : client_state) (act : EmptySet + ClientAPI) (st' : client_state) :=
      let (req, res) := st in
      match act with
      | inl e => match e with end
      | inr (inl (Put k v)) =>
        st' = (req ++ [Req_Put k v], res)
      | inr (inl (Get k)) =>
        st' = (req ++ [Req_Get k], res)
      | inr (inr (inl (Send m))) =>
        exists tl, req = m :: tl /\ st' = (tl, res)
      | inr (inr (inr (Recv m))) =>
        st' = (req, res ++ [m])
      | inr (inl (PutOk)) =>
        exists tl, res = Resp_Ok :: tl /\ st' = (req, tl)
      | inr (inl (GetResult v)) =>
        exists tl, res = (Resp_Value v) :: tl /\ st' = (req, tl)
      end.

    Definition Client : AutomatonDef ClientAPI :=
      mkAutomatonDef ClientAPI client_state EmptySet client_start client_step.

    Definition ServerAndChannels :=
      compose
        (compose
           Server
           (Channel.MediatedReliableReordering Request)
           (ChannelAPI Request + ChannelSenderAPI Response)
           (fun act => match act with
                       | inl (inl _) => None
                       | inl (inr act') => Some (inl act')
                       | inr act' => Some (inr act')
                       end)
           (fun act => match act with
                       | inl act' => Some act'
                       | inr _ => None
                       end)
        )
        (Channel.MediatedReliableReordering Response)
        (ChannelAPI Request + ChannelAPI Response)
        (fun act => match act with
                    | inl act' => Some (inl act')
                    | inr (inl act') => Some (inr act')
                    | inr (inr _) => None
                    end)
        (fun act => match act with
                    | inl _ => None
                    | inr act' => Some act'
                    end).

    Definition ServerAndFIFOChannels :=
      compose
        (compose
           Server
           (Channel.Reliable Request)
           (ChannelAPI Request + ChannelSenderAPI Response)
           (fun act => match act with
                       | inl (inl _) => None
                       | inl (inr act') => Some (inl act')
                       | inr act' => Some (inr act')
                       end)
           (fun act => match act with
                       | inl act' => Some act'
                       | inr _ => None
                       end)
        )
        (Channel.Reliable Response)
        (ChannelAPI Request + ChannelAPI Response)
        (fun act => match act with
                    | inl act' => Some (inl act')
                    | inr (inl act') => Some (inr act')
                    | inr (inr _) => None
                    end)
        (fun act => match act with
                    | inl _ => None
                    | inr act' => Some act'
                    end).

    Definition System' :=
      compose
        ServerAndChannels
        Client
        (API + (ChannelAPI Request + ChannelAPI Response))
        (fun act => match act with
                    | inl _ => None
                    | inr act' => Some act'
                    end)
        (fun act => match act with
                    | inl act' => Some (inl act')
                    | inr (inl (inl act')) => Some (inr (inl act'))
                    | inr (inl (inr _)) => None
                    | inr (inr (inl _)) => None
                    | inr (inr (inr act')) => Some (inr (inr act'))
                    end).

    Definition SystemFIFO' :=
      compose
        ServerAndFIFOChannels
        Client
        (API + (ChannelAPI Request + ChannelAPI Response))
        (fun act => match act with
                    | inl _ => None
                    | inr act' => Some act'
                    end)
        (fun act => match act with
                    | inl act' => Some (inl act')
                    | inr (inl (inl act')) => Some (inr (inl act'))
                    | inr (inl (inr _)) => None
                    | inr (inr (inl _)) => None
                    | inr (inr (inr act')) => Some (inr (inr act'))
                    end).

    Definition System :=
      rename
        System'
        API
        (fun act => inl act)
        (ChannelAPI Request + ChannelAPI Response)
        (fun act => inr act).

    Definition SystemFIFO :=
      rename
        SystemFIFO'
        API
        (fun act => inl act)
        (ChannelAPI Request + ChannelAPI Response)
        (fun act => inr act).

  End Main.

  Section SystemCorrect.

    Import Spec.

    Theorem System_correct : refines System Spec.KVStore.
    Proof.
      eapply refines_trans.
      - apply refines_rename.
        apply refines_comp_subst.
        eapply refines_trans.
        + apply refines_comp_subst.
          apply refines_comp_subst_r.
          apply Channel.reordering_mediator_correct.
        + apply refines_comp_subst_r.
          apply Channel.reordering_mediator_correct.
      - apply forward_simulation with
        (fun st_impl st_spec =>
           let s_req := requests st_spec in
           let s_res := responses st_spec in
           let s_d := data st_spec in
           let i_reqbuf := snd (fst (fst st_impl)) in
           let i_req := fst (snd st_impl) in
           let i_resbuf := snd (fst st_impl) in
           let i_res := snd (snd st_impl) in
           let i_ress := fst (fst (fst (fst st_impl))) in
           let i_d := snd (fst (fst (fst st_impl))) in

           s_req = i_reqbuf ++ i_req /\
           s_res = i_res ++ i_resbuf ++ i_ress /\
           (*
         (forall k, s_d k = i_d k)
            *)
           s_d = i_d
        ).
        split.
        + intros s Hs.
          repeat match goal with
                 | [ H : IOA.start _ _ |- _ ] => inversion H; clear H
                 end.
          destruct s as [[[[? ?] ?] ?] ?].
          simpl in *.
          cleanup; subst.
          unfold start; intuition; eauto.
        + intros s1' s1 act s2' Hstep Hrel.
          destruct act as [act | act].
          * (* channel stuff *)
            destruct act as [[[[[] | []] | []] | []] | act].
            destruct act as [[[] | [req]] | [[] | []]];
              try solve [
                    destruct s1 as [[[[? ?] ?] ?] ?];
                    destruct s1' as [[[[? ?] ?] ?] ?];
                    exists s2';
                    destruct s2';
                    simpl in *; intuition;
                    try match goal with
                        | [ H : client_step ?x _ _ |- _ ] =>
                          destruct x; simpl in H; inv_clear H
                        end;
                    cleanup; subst; simpl;
                    try crush_list; auto
                  ].
            destruct s1 as [[[[? ?] ?] ?] ?];
              destruct s1' as [[[[? ?] ?] ?] ?];
              destruct s2'.
            simpl in *.
            eexists (mkState _ _ _); intuition.
            subst.
            estep_int_break Execute; eauto.
            simpl; repeat eexists; eauto;
              destruct req; cleanup; subst;
                f_equal; crush_list.
          * (* API *)
            destruct act;
              destruct s1 as [[[[? ?] ?] ?] ?];
              destruct s1' as [[[[? ?] ?] ?] ?];
              destruct s2';
              simpl in *;
              eexists (mkState _ _ _); intuition;
                subst;
                estep_ext_break; eauto;
                  cleanup; subst; simpl in *;
                    try match goal with
                        | [ H : client_step ?x _ _ |- _ ] =>
                          destruct x; simpl in H; inv_clear H
                        end;
                    cleanup; subst; simpl;
                      try solve [eexists; eauto];
                      try solve [f_equal; crush_list].
    Qed.

  End SystemCorrect.

End ClientServer.

Module Sharded.

  Section Main.

    Import Channel.

    (* note: this doesn't refine Spec because it reorders stuff
       between the shards *)

    Inductive ShardRequest :=
    | Req_Put (k : nat) (v : nat)
    | Req_Get (k : nat)
    .

    Inductive ShardResponse :=
    | Resp_Ok
    | Resp_Value (v : option nat)
    .

    Definition ShardAPI : Type :=
      (ChannelReceiverAPI ShardRequest) + (ChannelSenderAPI ShardResponse).

    Definition shard_state : Type := (list ShardResponse) * (nat -> option nat).

    Definition shard_start (st : shard_state) : Prop :=
      st = ([], fun _ => None).

    Definition shard_step (st : shard_state) (act : EmptySet + ShardAPI) (st' : shard_state) :=
      let (resp, m) := st in
      match act with
      | inl e => match e with end
      | inr (inl (Recv (Req_Put k v))) =>
        st' = (resp ++ [Resp_Ok], fun k' => if eq_nat_dec k k' then Some v else m k')
      | inr (inl (Recv (Req_Get k))) =>
        st' = (resp ++ [Resp_Value (m k)], m)
      | inr (inr (Send msg)) =>
        exists tl, resp = msg :: tl /\ st' = (tl, m)
      end.

    Definition Shard : AutomatonDef ShardAPI :=
      mkAutomatonDef ShardAPI shard_state EmptySet shard_start shard_step.

    (* coordinator coordinates between 2 shards. overall API is:
    channel to S_even, channel from S_even, channel to S_odd, channel
    from S_odd, API *)
    Definition CoordinatorChannels : Type :=
      (ChannelSenderAPI ShardRequest + ChannelReceiverAPI ShardResponse) +
      (ChannelSenderAPI ShardRequest + ChannelReceiverAPI ShardResponse).
    Definition CoordinatorAPI : Type := API + CoordinatorChannels.

    Record coord_state : Type := mkCoordState {
                                     req_even : list ShardRequest;
                                     req_odd : list ShardRequest;
                                     resp : list ShardResponse
                                   }.

    Definition coord_start (st : coord_state) :=
      st = mkCoordState [] [] [].

    Definition coord_step (st : coord_state) (act : EmptySet + CoordinatorAPI) (st' : coord_state) : Prop :=
      let (re, ro, r) := st in
      match act with
      | inl e => match e with end

      (* input *)
      | inr (inl (Put k v)) =>
        if even_odd_dec k then
          st' = mkCoordState (re ++ [Req_Put k v]) ro r else
          st' = mkCoordState re (ro ++ [Req_Put k v]) r
      | inr (inl (Get k)) =>
        if even_odd_dec k then
          st' = mkCoordState (re ++ [Req_Get k]) ro r else
          st' = mkCoordState re (ro ++ [Req_Get k]) r

      (* even shard *)
      | inr (inr (inl (inl (Send m)))) =>
        exists tl, re = m :: tl /\ st' = mkCoordState tl ro r
      | inr (inr (inl (inr (Recv m)))) =>
        st' = mkCoordState re ro (r ++ [m])

      (* odd shard *)
      | inr (inr (inr (inl (Send m)))) =>
        exists tl, ro = m :: tl /\ st' = mkCoordState re tl r
      | inr (inr (inr (inr (Recv m)))) =>
        st' = mkCoordState re ro (r ++ [m])

      (* output *)
      | inr (inl PutOk) =>
        exists tl, r = Resp_Ok :: tl /\ st' = mkCoordState re ro tl
      | inr (inl (GetResult v)) =>
        exists tl, r = (Resp_Value v) :: tl /\ st' = mkCoordState re ro tl
      end.

    Definition Coordinator : AutomatonDef CoordinatorAPI :=
      mkAutomatonDef CoordinatorAPI coord_state EmptySet coord_start coord_step.

    Definition ShardAndChannels :=
      compose
        (compose
           Shard
           (Channel.Reliable ShardRequest)
           (ChannelAPI ShardRequest + ChannelSenderAPI ShardResponse)
           (fun act => match act with
                       | inl (inl _) => None
                       | inl (inr act') => Some (inl act')
                       | inr act' => Some (inr act')
                       end)
           (fun act => match act with
                       | inl act' => Some act'
                       | inr _ => None
                       end)
        )
        (Channel.Reliable ShardResponse)
        (ChannelAPI ShardRequest + ChannelAPI ShardResponse)
        (fun act => match act with
                    | inl act' => Some (inl act')
                    | inr (inl act') => Some (inr act')
                    | inr (inr _) => None
                    end)
        (fun act => match act with
                    | inl _ => None
                    | inr act' => Some act'
                    end).

  End Main.

End Sharded.
