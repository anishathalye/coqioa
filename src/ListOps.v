Require Import Automation.

Require Import List.
Import ListNotations.
Require Import Permutation.

Section Main.

  Variable A : Type.
  Hypothesis Aeq_dec : forall x x' : A, {x = x'} + {x <> x'}.

  Fixpoint remove_one (x : A) (l : list A) : list A :=
    match l with
    | [] => nil
    | y :: ys => if (Aeq_dec x y) then ys else y :: remove_one x ys
    end.

  Lemma remove_one_only : forall x,
      remove_one x [x] = [].
  Proof.
    intros x; simpl.
    destruct (Aeq_dec x x); shallow.
  Qed.

  Lemma remove_different_not_in : forall (x y : A) (l : list A),
    x <> y ->
    ~ In x (remove_one y l) ->
    ~ In x l.
  Proof with shallow.
    intros x y l Hneq H.
    induction l; auto.
    simpl.
    intros contra.
    destruct (Aeq_dec a x); subst; simpl in *.
    - destruct (Aeq_dec y x)...
    - inversion contra;
      destruct (Aeq_dec y a)...
  Qed.

  Lemma remove_different_in : forall (x y : A) (l : list A),
    x <> y ->
    In x (remove_one y l) ->
    In x l.
  Proof with shallow.
    intros x y l Hneq H.
    induction l; auto.
    simpl.
    destruct (Aeq_dec a x); subst; simpl in *.
    - destruct (Aeq_dec y x)...
    - destruct (Aeq_dec y a)...
  Qed.

  Lemma remove_one_different_count : forall (x y : A) (l : list A),
    x <> y ->
    count_occ Aeq_dec l y = count_occ Aeq_dec (remove_one x l) y.
  Proof.
    intros.
    induction l; auto.
    simpl.
    destruct (Aeq_dec a y); subst;
    repeat (destruct (Aeq_dec _ _); simpl; shallow).
  Qed.

  Lemma remove_one_dec_count : forall (x : A) (l : list A),
    In x l ->
    count_occ Aeq_dec l x = count_occ Aeq_dec (remove_one x l) x + 1.
  Proof.
    intros.
    induction l; simpl; shallow.
    destruct (Aeq_dec a x); subst.
    destruct (Aeq_dec _ _); shallow.
    destruct (Aeq_dec _ _); shallow.
    simpl.
    destruct (Aeq_dec _ _); shallow.
  Qed.

  Inductive contains (x : A) : list A -> Prop :=
  | contains_here : forall xs,
      contains x (x :: xs)
  | contains_inside : forall y xs,
      contains x xs ->
      contains x (y :: xs).

  Lemma contains_In :
    forall x xs,
      contains x xs <-> In x xs.
  Proof.
    intros x xs.
    split.
    - intros Hct.
      induction Hct; simpl; auto.
    - intros Hin.
      induction xs; inversion Hin; subst; constructor; auto.
  Qed.

  Lemma contains_perm :
    forall x xs ys,
      contains x xs ->
      Permutation xs ys ->
      contains x ys.
  Proof.
    intros x xs ys Hct Hperm.
    apply contains_In.
    eapply Permutation_in; eauto.
    apply contains_In; auto.
  Qed.

  Lemma contains_app :
    forall x xs ys,
      contains x xs ->
      contains x (xs ++ ys).
  Proof.
    intros x xs ys Hct.
    induction Hct.
    - simpl; constructor.
    - constructor; auto.
  Qed.

  Inductive removed (x : A) : list A -> list A -> Prop :=
  | removed_here : forall xs,
      removed x (x :: xs) xs
  | removed_inside : forall y xs ys,
      removed x xs ys ->
      removed x (y :: xs) (y :: ys).

  Lemma removed_perm : forall x xs xs',
      removed x xs xs' ->
      Permutation xs (x :: xs').
  Proof.
    intros x xs xs' H.
    induction H.
    - auto.
    - eapply perm_trans with (y :: x :: ys).
      + eauto.
      + constructor.
  Qed.

  Lemma removed_contains : forall x xs ys,
      removed x xs ys ->
      contains x xs.
  Proof.
    induction 1; simpl; econstructor; auto.
  Qed.

  Inductive one_removed_pred (pred : A -> Prop) : list A -> list A -> Prop :=
  | one_removed_pred_here : forall x xs,
      pred x ->
      one_removed_pred pred (x :: xs) xs
  | one_removed_pred_inside : forall x xs ys,
      one_removed_pred pred xs ys ->
      one_removed_pred pred (x :: xs) (x :: ys).

  Inductive one_removed : list A -> list A -> Prop :=
  | one_removed_here : forall x xs,
      one_removed (x :: xs) xs
  | one_removed_inside : forall x xs ys,
      one_removed xs ys ->
      one_removed (x :: xs) (x :: ys).

  Inductive one_changed (f : A -> A) : list A -> list A -> Prop :=
  | one_changed_here : forall x xs,
      one_changed f (x :: xs) (f x :: xs)
  | one_changed_inside : forall x xs ys,
      one_changed f xs ys ->
      one_changed f (x :: xs) (x :: ys).

  Inductive subsequence_pred (pred : A -> Prop) : list A -> list A -> Prop :=
  | subsequence_pred_empty : subsequence_pred pred [] []
  | subsequence_pred_keep : forall orig smaller x,
      subsequence_pred pred orig smaller ->
      subsequence_pred pred (x :: orig) (x :: smaller)
  | subsequence_pred_drop : forall orig smaller x,
      pred x ->
      subsequence_pred pred orig smaller ->
      subsequence_pred pred (x :: orig) smaller.

  Inductive subsequence : list A -> list A -> Prop :=
  | subsequence_empty : subsequence [] []
  | subsequence_keep : forall orig smaller x,
      subsequence orig smaller ->
      subsequence (x :: orig) (x :: smaller)
  | subsequence_drop : forall orig smaller x,
      subsequence orig smaller ->
      subsequence (x :: orig) smaller.

  Inductive sub_changed (f : A -> A) : list A -> list A -> Prop :=
  | sub_changed_empty : sub_changed f [] []
  | sub_changed_keep : forall orig changed x,
      sub_changed f orig changed ->
      sub_changed f (x :: orig) (x :: changed)
  | sub_changed_change : forall orig changed x,
      sub_changed f orig changed ->
      sub_changed f (x :: orig) (f x :: changed).

  Lemma app_head : forall (l1 l2 l3 : list A),
      l2 = l3 -> l1 ++ l2 = l1 ++ l3.
  Proof.
    induction 1; auto.
  Qed.

  Lemma app_tail : forall (l1 l2 l3 : list A),
      l2 = l3 -> l2 ++ l1 = l3 ++ l1.
  Proof.
    induction 1; auto.
  Qed.

End Main.

Arguments contains {A}.
Arguments removed {A}.
Arguments one_removed_pred {A}.
Arguments one_removed {A}.
Arguments one_changed {A}.
Arguments subsequence_pred {A}.
Arguments subsequence {A}.
Arguments sub_changed {A}.
Hint Constructors contains.
Hint Constructors removed.
Hint Constructors one_removed_pred.
Hint Constructors one_removed.
Hint Constructors one_changed.
Hint Constructors subsequence_pred.
Hint Constructors subsequence.
Hint Constructors sub_changed.

Ltac crush_list :=
  match goal with
  | [ |- ?a ++ ?b :: ?c = (?a ++ [?b]) ++ ?c ] =>
    solve [rewrite <- app_assoc; reflexivity]
  | [ |- ?a ++ ?b = ?a ++ ?c ] => apply app_head; try crush_list
  | [ |- ?a ++ ?x = ?b ++ ?x ] => apply app_tail; try crush_list
  | [ |- ?x ++ ?y ++ ?z ++ ?w = (?x ++ ?y ++ ?z) ++ ?w] =>
    rewrite <- app_assoc; apply app_head; try crush_list
  | [ |- ?x ++ ?y ++ ?z = (?x ++ ?y) ++ ?z ] =>
      rewrite <- app_assoc; apply app_head; try crush_list
  | [ |- _ ] => solve [auto]
  end.
