Require Import List.
Require Import Eqdep.

Variant EmptySet : Set := .

Lemma list_map_map : forall (T U V: Type) (xs : list T) (f : T -> U) (g : U -> V),
    map g (map f xs) = map (fun x => g (f x)) xs.
Proof.
  intros T U V xs f g.
  induction xs; auto.
  simpl; rewrite IHxs; auto.
Qed.

Lemma map_replace : forall (T U : Type) (xs : list T) (f f' : T -> U),
    (forall x, f x = f' x) ->
    map f xs = map f' xs.
Proof.
  intros T U xs f f' Heq.
  induction xs as [| x xs']; auto.
  simpl; rewrite IHxs'; rewrite (Heq x); auto.
Qed.

Lemma map_id : forall (T : Type) (xs : list T),
    map id xs = xs.
Proof.
  intros T xs.
  induction xs; auto.
  simpl; rewrite IHxs; auto.
Qed.

Fixpoint flatmap {A B : Type} (f : A -> option B) (l : list A) :=
  match l with
  | nil => nil
  | x :: xs => match f x with
               | None => flatmap f xs
               | Some x' => x' :: flatmap f xs
               end
  end.

Lemma plus_1_r : forall n,
    n + 1 = S n.
Proof.
  intros n; induction n; simpl; auto.
Qed.

Lemma nil_eq_app : forall (T : Type) (xs ys : list T),
    nil = xs ++ ys ->
    xs = nil /\ ys = nil.
Proof.
  intros T xs ys H.
  induction xs.
  - auto.
  - inversion H.
Qed.
