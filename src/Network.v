Require Import IOA.
Require Import ListOps.
Require Import Automation.

Require Import List.

Section Main.

  Variable Address : Type.
  Variable Message : Type.
  Variable Address_eq_dec : forall (x y : Address), {x = y} + {x <> y}.
  Variable Message_eq_dec : forall (x y : Message), {x = y} + {x <> y}.

  Inductive Network_API :=
  (* from point of view of users of network service *)
  | Send : Address -> Message -> Address -> Network_API (* input to network ioa *)
  | Recv : Address -> Message -> Address -> Network_API. (* output from network ioa *)

  Inductive Network_Internal :=
  | Drop : Network_Internal.

  Definition Network_actions : Type := Network_Internal + Network_API.

  Record Packet := mkPacket {
                       src : Address ;
                       msg : Message ;
                       dst : Address
                     }.

  Definition Packet_eq_dec : forall (x y : Packet), {x = y} + {x <> y}.
    intros x y.
    decide equality.
  Defined.

  Definition Network_state : Type := list Packet. (* the buffer *)

  Definition Network_transition (st : Network_state) (act : Network_actions) (st' : Network_state) : Prop :=
    match act with
    | inr (Send src msg dst) => st' = (mkPacket src msg dst) :: st
    | inr (Recv src msg dst) => let pkt := mkPacket src msg dst in
                                In pkt st /\ st' = remove_one _ Packet_eq_dec pkt st
    | inl Drop => exists pkt, In pkt st /\ st' = remove_one _ Packet_eq_dec pkt st
    end.

  Definition Network_init (st : Network_state) := st = nil.

  Definition Network : AutomatonDef Network_API :=
    mkAutomatonDef
      Network_API
      Network_state
      Network_Internal
      Network_init
      Network_transition.

End Main.

Arguments Send [Address Message].
Arguments Recv [Address Message].
Arguments mkPacket [Address Message].
