Reserved Notation "M '[' K ':=' V ']'" (no associativity, at level 91).

Reserved Notation "s '==>' s'" (at level 40).

Reserved Notation "s '==>*' s'" (at level 40).

Reserved Notation "s '=t>' s' '$' tr" (at level 40).

Reserved Notation "s '=t>*' s' '$' tr" (at level 40).

(* for the and/or below, we can't just return c1/c2 cause that makes
the return type of the if dependent on the condition, and we have no
need to do that *)

Notation "c1 '.|' c2" :=
  (if c1 then true else (if c2 then true else false))
    (at level 50, left associativity).

Notation "c1 '.&' c2" :=
  (if c1 then (if c2 then true else false) else false)
    (at level 40, left associativity).

Definition xor (P Q : Prop) : Prop := (P /\ ~ Q) \/ (~ P /\ Q).

Notation "P '\X/' Q" :=
  (xor P Q)
    (at level 85, right associativity).
