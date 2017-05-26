Require Omega.
Require Import Znumtheory.
Require Import BinInt.
Require Import List.

Tactic Notation "solve" "by" "contradiction" :=
  match goal with
  | H : _ |- _ => solve [ contradiction H; subst; auto ]
  end
  || fail "because the goal is not solvable by contradiction.".

Tactic Notation "rep_destruct_step" tactic(t) :=
  match goal with
  | H : _ |- _ => destruct H; t
  end.

Tactic Notation "rep_destruct" "1" tactic(t) :=
  rep_destruct_step t.

Tactic Notation "rep_destruct" "2" tactic(t) :=
  rep_destruct_step (rep_destruct 1 t).

Tactic Notation "rep_destruct" "2" tactic(t) :=
  rep_destruct_step (rep_destruct 2 t).

Tactic Notation "rep_destruct" tactic(t) :=
  rep_destruct 1 t.

(* solve by inversion adapted from Benjamin Pierce's Software Foundations *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; auto; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(* --- *)

Ltac shallow :=
  let ss := simpl in *; intuition; try subst in

  auto;
  try (ss; solve by contradiction);
  try (ss; solve by inversion).

Ltac Zltb_conv := repeat (match goal with
| [ H: (_ <? _) = true |- _ ] => rewrite Z.ltb_lt in H
| [ H: (_ <? _) = false |- _ ] => rewrite Z.ltb_nlt in H
| [ H: _ |- (_ <? _) = true ] => rewrite Z.ltb_lt
| [ H: _ |- (_ <? _) = false ] => rewrite Z.ltb_nlt
end).

Ltac explode' :=
  match goal with
  | [ H : _ /\ _ |- _ ] => inversion H; clear H
  | [ H : pair _ _ = pair _ _ |- _ ] => inversion H; clear H
  end.

Ltac break_or :=
  match goal with
  | [ H : _ \/ _ |- _ ] => inversion H; clear H
  end.

Ltac explode := repeat explode'.

Ltac safe_intuition :=
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H1 : ?P -> _, H2 : ?P |- _ ] =>
           let t := type of P in
           lazymatch t with
           | Prop => specialize (H1 H2)
           | _ => fail
           end
         end.

Ltac deex :=
  match goal with
  | [ H: exists (name:_), _ |- _ ] =>
    let name := fresh name in
    destruct H as [name ?];
    safe_intuition
  end.

Ltac subst_evars :=
  (* this might be a bit fragile *)
  repeat match goal with
         | [ var := ?value |- _ ] => subst var
         end.

Lemma exists_lift_l :
  forall (T : Type) (P : T -> Prop) (Q : Prop),
    (exists x, P x) ->
    Q ->
    exists x, P x /\ Q.
Proof.
  intuition; deex; eauto.
Qed.

Lemma exists_lift_r :
  forall (T : Type) (P : T -> Prop) (Q : Prop),
    Q ->
    (exists x, P x) ->
    exists x, Q /\ P x.
Proof.
  intuition; deex; eauto.
Qed.

Ltac exists_lift :=
  match goal with
  | [ |- exists x, ?P /\ ?Q ] => first [apply exists_lift_l | apply exists_lift_r]
  end.

Ltac rw :=
  match goal with
  | [ H : ?x = ?y |- context[?y] ] => rewrite <- H
  | [ H : ?x = ?y |- context[?x] ] => rewrite H
  end.

Ltac break_cons_eq :=
  match goal with
  | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; clear H
  end.

Ltac remove_useless :=
  repeat match goal with
         | [ H : ?x = ?x |- _ ] => clear H
         | [ H : ?x = ?y, H' : ?y = ?x |- _ ] => clear H'
         | [ H : ?x, H' : ?x |- _ ] => clear H'
         | [ H : True |- _ ] => clear H
         end.

Ltac cleanup :=
  repeat deex;
  repeat break_cons_eq;
  explode;
  remove_useless.

Lemma match_inl : forall A B (P1 : A -> Prop) (P2 : B -> Prop) a x,
    x = inl a ->
    P1 a ->
    match x with
    | inl a' => P1 a'
    | inr b => P2 b
    end.
Proof.
  intros; subst; auto.
Qed.

Lemma match_inr : forall A B (P1 : A -> Prop) (P2 : B -> Prop) b x,
    x = inr b ->
    P2 b ->
    match x with
    | inl a => P1 a
    | inr b' => P2 b'
    end.
Proof.
  intros; subst; auto.
Qed.

Ltac inv_clear H :=
  inversion H; clear H.

Ltac solve_match :=
  try solve [eapply match_inl; eauto];
  try solve [eapply match_inr; eauto].

Ltac inst_rec_prod T cont :=
  lazymatch eval simpl in T with
  | prod ?A ?B =>
    inst_rec_prod
      A
      ltac:(fun left =>
              inst_rec_prod
                B
                ltac:(fun right => cont (left, right)))
  | _ => let x := fresh "x" in
         evar (x : T); cont x; clear x
  end.

Ltac ebreak_prod :=
  repeat match goal with
         | [ |- context[ ?x ] ] =>
           is_evar x;
           let T := type of x in
           (* we check the type here even though it happens in
              inst_rec_prod, because we want the ebreak_prod top level
              repeat to get all the separate evars but we don't want
              it to loop forever *)
           lazymatch eval simpl in T with
           | prod _ _ => inst_rec_prod T ltac:(fun x' => unify x x')
           end
         end.

Ltac destruct_prod :=
  repeat match goal with
         | [ x : prod _ _ |- _ ] => destruct x
         end.

(* taken from https://github.com/mit-pdos/fscq, written by Tej Chajed <tchajed@mit.edu> *)
Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
          let repl_match_hyp H d d' :=
              replace d with d' in H;
              lazymatch type of H with
              | context[match d' with _ => _ end] => fail
              | _ => idtac
              end in
                  match goal with
                  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
                    repl_match_goal d d'
                  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
                    repl_match_goal d d'
                  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
                    repl_match_hyp H d d'
                  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
                    repl_match_hyp H d d'
                  end.
