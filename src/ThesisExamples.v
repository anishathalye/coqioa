Require Import IOA.
Require Import Automation.
Require Import ListOps.
Require Import Misc.

Require Import List.
Import ListNotations.

Module LossyFifo.

  Section Main.

    Variable T : Type.

    Inductive ChannelAPI :=
    | Send (m : T)
    | Recv (m : T).

    Inductive Internal :=
    | Drop (m : T).

    Definition LossyFifo : AutomatonDef ChannelAPI :=
      mkAutomatonDef
        _
        (list T) (* state: list of messages *)
        Internal
        (fun st => st = []) (* start state: empty queue *)
        (* transition relation: *)
        (fun st act st' =>
           match act with
           | inl (Drop m) => contains m st /\ removed m st st'
           | inr (Send m) => st' = st ++ [m]
           | inr (Recv m) => st = m :: st'
           end).

  End Main.

  Arguments LossyFifo {T}.
  Arguments Send {T}.
  Arguments Recv {T}.
  Arguments Drop {T}.

  Goal in_traces LossyFifo [Send 1; Send 2; Recv 2].
  Proof with simpl; intuition; auto.
    eexists; exists_lift; [simpl; auto |].
    eexists.
    eapply Step_External...
    eapply Step_External...
    eapply Step_Internal with (int := Drop _)...
    eapply Step_External...
  Qed.

End LossyFifo.
