Require Import IOA.
Require Import Misc.
Require Import Automation.

Require Import Eqdep_dec.
Require Import List.

Definition backward_simulation_relation {T} {def1 def2 : AutomatonDef T}
           (b : def1.(StateType) -> def2.(StateType) -> Prop) :=
  (forall s1, exists s2, b s1 s2) /\
  (forall s1 s2,
      def1.(start) s1 ->
      b s1 s2 ->
      def2.(start) s2) /\
  (forall s1' s1 act1 s2,
      automaton_step _ s1' act1 s1 ->
      b s1 s2 ->
      exists s2', b s1' s2' /\
                  valid_execution_fragment _ s2' s2 (match act1 with
                                                     | inl int => nil
                                                     | inr ext => ext :: nil
                                                     end)).

Lemma backward_simulation_reconstruct :
  forall {T} {def1 def2 : AutomatonDef T}
         b s1' s1 acts s2,
    backward_simulation_relation b ->
    valid_execution_fragment def1 s1' s1 acts ->
    b s1 s2 ->
    exists s2',
      b s1' s2' /\ valid_execution_fragment def2 s2' s2 acts.
Proof.
  intros T def1 def2 b s1' s1 acts s2.
  intros Hbackward Htrace1 Hrelfinal.
  inversion Hbackward as [Hrel_exists [Hrel_start Htrace]].
  induction Htrace1; subst; eauto;
    specialize (IHHtrace1 Hrelfinal);
    inversion IHHtrace1 as [s2'' [Hs2''rel Hs2''valid]];
    specialize (Htrace st st'' _  s2'' H Hs2''rel);
    inversion Htrace as [s2' [Hs2'rel Hs2'valid]];
    eauto.
Qed.

Theorem backward_simulation :
  forall {T} (def1 def2 : AutomatonDef T),
  forall (b : def1.(StateType) -> def2.(StateType) -> Prop),
    backward_simulation_relation b ->
    refines def1 def2.
Proof.
  intros T def1 def2.
  intros b Hbackward.
  unfold refines.
  intros acts Htrace1.
  inversion Htrace1 as [s1init [s1final [Hstart1 Hfrag1]]].
  unfold in_traces.
  inversion Hbackward as [Hrel_exists [Hrel_start Htrace]].
  specialize (Hrel_exists s1final).
  inversion Hrel_exists as [s2final Hrels2final].
  pose proof (backward_simulation_reconstruct
                b
                s1init
                s1final
                acts
                s2final
                Hbackward
                Hfrag1
                Hrels2final) as [s2init Hs2].
  repeat eexists; intuition; eauto.
Qed.

Definition forward_simulation_relation {T} {def1 def2 : AutomatonDef T}
           (f : def1.(StateType) -> def2.(StateType) -> Prop) :=
  (forall s1,
      def1.(start) s1 ->
      exists s2, def2.(start) s2 /\ f s1 s2) /\
  (forall s1' s1 act1 s2',
      automaton_step _ s1' act1 s1 ->
      f s1' s2' ->
      exists s2, f s1 s2 /\
                 valid_execution_fragment _ s2' s2 (match act1 with
                                                    | inl int => nil
                                                    | inr ext => ext :: nil
                                                    end)).

(* inductive invariant -- something based on reachability (plain old
`invariant` rather than `invariant_ind`) would be stronger, but it's
slightly more effort and probably won't be used that commonly *)
Definition forward_simulation_relation_inv_ind {T} {def1 def2 : AutomatonDef T}
           (f : def1.(StateType) -> def2.(StateType) -> Prop)
           (inv : def1.(StateType) -> Prop) :=
  (invariant_ind _ inv) /\
  (forall s1,
      def1.(start) s1 ->
      exists s2, def2.(start) s2 /\ f s1 s2) /\
  (forall s1' s1 act1 s2',
      inv s1' ->
      automaton_step _ s1' act1 s1 ->
      f s1' s2' ->
      exists s2, f s1 s2 /\
                 valid_execution_fragment _ s2' s2 (match act1 with
                                                    | inl int => nil
                                                    | inr ext => ext :: nil
                                                    end)).

Lemma forward_simulation_inv_ind_reconstruct :
  forall {T} {def1 def2 : AutomatonDef T}
         f inv s1' s1 acts s2',
    forward_simulation_relation_inv_ind f inv ->
    valid_execution_fragment def1 s1' s1 acts ->
    inv s1' ->
    f s1' s2' ->
    exists s2,
      f s1 s2 /\ valid_execution_fragment def2 s2' s2 acts.
Proof.
  intros def1 def2 action_map f inv s1' s1 acts s2'.
  intros Hforward Htrace1 Hrelinit.
  inversion Hforward as [Hinv [_ Hrel_trace]].
  generalize dependent s2'.
  induction Htrace1; subst; eauto; intros s2' Hrel;
    destruct Hinv as [Hinvstart Hinvstep];
    assert (inv st) as Hinvst by eauto;
    assert (inv st'') as Hinvst'' by eauto;
    specialize (Hrel_trace st st'' _ s2' Hinvst H Hrel);
    inversion Hrel_trace as [s2'' [Hs2''rel Hs2''valid]];
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''rel);
    inversion IHHtrace1 as [s2 Hs2];
    eexists; subst; intuition; eauto.
Qed.

Theorem forward_simulation_inv_ind :
  forall {T} (def1 def2 : AutomatonDef T),
  forall (f : def1.(StateType) -> def2.(StateType) -> Prop)
         (inv : def1.(StateType) -> Prop),
    forward_simulation_relation_inv_ind f inv ->
    refines def1 def2.
Proof.
  intros def1 def2 action_map f inv Hforward.
  unfold refines.
  intros acts Htrace1.
  unfold in_traces in *.
  destruct Htrace1 as [s1init [s1final [Hstart1 Hfrag1]]].
  inversion Hforward as [[Hrel_inv_start _] [Hrel_start Hrel_trace]].
  specialize (Hrel_start s1init Hstart1).
  inversion Hrel_start as [s2init [Hs2start Hs2rel]].
  assert (inv s1init) as Hinvs1init by eauto.
  pose proof (forward_simulation_inv_ind_reconstruct
                f
                inv
                s1init
                s1final
                acts
                s2init
                Hforward
                Hfrag1
                Hinvs1init
                Hs2rel) as [s2final Hs2final].
  repeat eexists; intuition; eauto.
Qed.

Theorem forward_simulation :
  forall (E : Type) (A' A : AutomatonDef E)
         (f : (StateType A') -> (StateType A) -> Prop),
    forward_simulation_relation f ->
    refines A' A.
Proof.
  intros.
  eapply (forward_simulation_inv_ind _ _ _ (fun _ => True)).
  unfold forward_simulation_relation in *;
    unfold forward_simulation_relation_inv_ind;
    cleanup;
    unfold invariant_ind;
    split;
    eauto.
Qed.

Lemma refines_trans :
  forall {T} (def1 def2 intermediate : AutomatonDef T),
    refines def1 intermediate ->
    refines intermediate def2 ->
    refines def1 def2.
Proof.
  unfold refines; auto.
Qed.

Theorem forward_and_backward_simulation :
  forall {T} (def1 def2 intermediate : AutomatonDef T)
         (f : def1.(StateType) -> intermediate.(StateType) -> Prop)
         (b : intermediate.(StateType) -> def2.(StateType) -> Prop),
    forward_simulation_relation f ->
    backward_simulation_relation b ->
    refines def1 def2.
Proof.
  intros.
  eapply refines_trans.
  - eapply forward_simulation; eauto.
  - eapply backward_simulation; eauto.
Qed.
