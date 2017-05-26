Require Import IOA.
Require Import Automation.
Require Import Misc.
Require Import ListOps.
Require Import Simulation.

Require Import List.
Require Import Peano_dec.
Import ListNotations.

Module Api.

  Inductive Counter_API :=
  | Reset
  | Reset_Done
  | Increment
  | Increment_Done
  | Read_Request
  | Read_Response (value : nat).

End Api.

Module Blocking.

  Import Api.

  Inductive pc := Ready | Resetting | Incrementing | Reading.

  Definition state : Set := pc * nat.

  Definition transition (st : state) (act : EmptySet + Counter_API) (st' : state) : Prop :=
    match act with
    | inr Reset => (fst st = Ready /\ st' = (Resetting, snd st)) \/
                   (fst st <> Ready /\ st' = st)
    | inr Reset_Done => fst st = Resetting /\ st' = (Ready, 0)
    | inr Increment => (fst st = Ready /\ st' = (Incrementing, snd st)) \/
                       (fst st <> Ready /\ st' = st)
    | inr Increment_Done => fst st = Incrementing /\ st' = (Ready, S (snd st))
    | inr Read_Request => (fst st = Ready /\ st' = (Reading, snd st)) \/
                          (fst st <> Ready /\ st' = st)
    | inr (Read_Response n) => st = (Reading, n) /\ st' = (Ready, n)
    | inl f => match f with end
    end.

  Definition init value := value = (Ready, 0).

  Definition Spec : AutomatonDef Counter_API :=
    mkAutomatonDef _ state _ init transition.

  Goal in_traces Spec
       [
         Increment;
           Increment_Done;
           Read_Request;
           Read_Response 1;
           Increment;
           Increment_Done;
           Read_Request;
           Read_Response 2;
           Reset;
           Reset_Done;
           Read_Request;
           Read_Response 0
       ].
  Proof.
    eexists; eexists; split;
      [ cbv; eauto |
        repeat (eapply Step_External; simpl; eauto); econstructor; eauto ].
  Qed.

End Blocking.

Module Sequential.

  Import Api.

  Inductive op := Op_Reset | Op_Increment | Op_Read.

  Definition state := prod (list op) nat.

  Definition transition (st : state) (act : EmptySet + Counter_API) (st' : state) : Prop :=
    match act with
    | inr Reset => st' = (fst st ++ [Op_Reset], snd st)
    | inr Increment => st' = (fst st ++ [Op_Increment], snd st)
    | inr Read_Request => st' = (fst st ++ [Op_Read], snd st)
    | inr Reset_Done => fst st = Op_Reset :: fst st' /\
                        snd st' = 0
    | inr Increment_Done => fst st = Op_Increment :: fst st' /\
                            snd st' = S (snd st)
    | inr (Read_Response n) => fst st = Op_Read :: fst st' /\
                               n = snd st /\
                               snd st' = snd st
    | inl f => match f with end
    end.

  Definition init (st : state) := st = ([], 0).

  Definition Spec : AutomatonDef Counter_API :=
    mkAutomatonDef _ state _ init transition.

  (* overlapping requests -- this trace would not be allowed by the
     blocking spec *)
  Goal in_traces Spec
       [
         Increment; (* input 1 *)
           Read_Request; (* input 2 *)
           Increment_Done; (* output 1 *)
           Increment; (* input 3 *)
           Read_Response 1; (* output 2 *)
           Increment_Done; (* output 3 *)
           Read_Request; (* input 4 *)
           Reset; (* input 5 *)
           Read_Response 2; (* output 4 *)
           Reset_Done; (* output 5 *)
           Read_Request; (* input 6 *)
           Read_Response 0 (* output 6 *)
       ].
  Proof.
    unfold in_traces.
    eexists; exists_lift; [cbv; eauto |].
    eexists.
    repeat (
        estep_ext_break;
        try match goal with
            | [ |- context[ ?x ] ] =>
              is_evar x;
              let T := type of x in
              lazymatch eval simpl in T with
              | state => inst_rec_prod (prod (list op) nat) ltac:(fun x' => unify x x')
              end
            end;
        simpl; intuition; eauto
      ).
  Qed.

End Sequential.

Module MultiClientApi.

  Inductive Counter_API :=
  | Reset (cid : nat)
  | Reset_Done (cid : nat)
  | Increment (cid : nat)
  | Increment_Done (cid : nat)
  | Read_Request (cid : nat)
  | Read_Response (cid : nat) (value : nat).

End MultiClientApi.

Module Linearizable.

  Import MultiClientApi.

  Inductive op := Op_Reset | Op_Increment | Op_Read.
  Inductive resp := Resp_Reset | Resp_Increment | Resp_Read (value : nat).

  (* client id -> pending requests, counter *)
  Record state := mkState {
                      requests : nat -> list op;
                      responses : nat -> list resp;
                      counter : nat
                    }.

  Inductive Internal := Execute.

  Definition transition (st : state) (act : Internal + Counter_API) (st' : state) : Prop :=
    let (req, resp, n) := st in
    match act with
    | inr (Reset cid) => st' = mkState
                                 (fun x => if eq_nat_dec cid x
                                           then req cid ++ [Op_Reset]
                                           else req x)
                                 resp
                                 n
    | inr (Increment cid) => st' = mkState
                                     (fun x => if eq_nat_dec cid x
                                               then req cid ++ [Op_Increment]
                                               else req x)
                                     resp
                                     n
    | inr (Read_Request cid) => st' = mkState
                                        (fun x => if eq_nat_dec cid x
                                                  then req cid ++ [Op_Read]
                                                  else req x)
                                        resp
                                        n
    | inr (Reset_Done cid) => exists tl, resp cid = Resp_Reset :: tl /\
                                         st' = mkState
                                                 req
                                                 (fun x => if eq_nat_dec cid x
                                                           then tl
                                                           else resp x)
                                                 n
    | inr (Increment_Done cid) => exists tl, resp cid = Resp_Increment :: tl /\
                                             st' = mkState
                                                     req
                                                     (fun x => if eq_nat_dec cid x
                                                               then tl
                                                               else resp x)
                                                     n
    | inr (Read_Response cid v) => exists tl, resp cid = (Resp_Read v) :: tl /\
                                              st' = mkState
                                                      req
                                                      (fun x => if eq_nat_dec cid x
                                                                then tl
                                                                else resp x)
                                                      n
    | inl Execute => exists cid op tl, req cid = op :: tl /\
                                       st' = mkState
                                               (fun x => if eq_nat_dec cid x
                                                         then tl
                                                         else req x)
                                               (fun x => if eq_nat_dec cid x then
                                                           resp cid ++ match op with
                                                                       | Op_Reset => [Resp_Reset]
                                                                       | Op_Increment => [Resp_Increment]
                                                                       | Op_Read => [Resp_Read n]
                                                                       end
                                                         else resp x)
                                               match op with
                                               | Op_Increment => n + 1
                                               | _ => n
                                               end
    end.

  Definition init (st : state) :=
    st = mkState (fun _ => nil) (fun _ => nil) 0.

  Definition Spec : AutomatonDef Counter_API :=
    mkAutomatonDef _ state _ init transition.

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
        evar (x1 : nat -> list op);
        evar (x2 : nat -> list resp);
        evar (x3 : nat);
        unify x (mkState x1 x2 x3);
        clear x1 x2 x3
      end
    end.

  Tactic Notation "ext" :=
    estep_ext_break; [solve [break_state; cbv; eauto] |].

  Tactic Notation "int" uconstr(client) :=
    estep_int_break Execute; [
      solve [break_state; simpl; exists client; eexists; eexists; simpl; auto] |].

  Ltac linearization ls :=
    first [
        lazymatch ls with
        | ?h :: ?t => int h; linearization t
        | _ => fail
        end |
        ext; linearization ls |
        solve [eauto]
      ].

  Goal in_traces Spec
       [
         Increment 1;
           Increment 2;
           Increment 3;
           Read_Request 1;
           Read_Request 3;
           Increment_Done 1;
           Increment_Done 2;
           Increment_Done 3;
           Read_Response 1 1; (* even though client 1 reads "1", it's still linearizable *)
           Read_Response 3 3
       ].
  Proof.
    unfold in_traces.
    eexists; exists_lift; [cbv; eauto |].
    eexists.
    linearization [1; 1; 2; 3; 3]. (* another valid linearization would be [1; 1; 3; 2; 3] *)
  Qed.

End Linearizable.
