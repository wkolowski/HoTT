(** This file is based on the paper "Infinite sets that satisfy the principle
    of omniscience in any variety of constructive mathematics" by
    Martin Escardó. *)

Definition omniscient (X : Type) : Prop :=
  forall p : X -> bool,
    (exists x : X, p x = false) \/ forall x : X, p x = true.

Inductive leb : bool -> bool -> Prop :=
    | leb_refl : forall b : bool, leb b b
    | leb_ft : leb false true.

Definition conat : Type :=
  {a : nat -> bool | forall n : nat, leb (a (S n)) (a n)}.

Definition selection_function {X : Type} (e : (X -> bool) -> X) : Prop :=
  forall p : X -> bool, p (e p) = true -> forall x : X, p x = true.

Definition searchable (X : Type) : Prop :=
  exists e : (X -> bool) -> X, selection_function e.

(** Lemma 2.2 *)
Lemma searchable_omniscient :
  forall X : Type,
    searchable X -> omniscient X.
Proof.
Admitted.

(** Lemma 2.3 *)
Lemma lemma_2_3 :
  forall (X : Type) (e : (X -> bool) -> X) (p : X -> bool),
    selection_function e ->
      (exists x : X, p x = false) <-> p (e p) = false.
Proof.
Admitted.

(** Proposition 2.4 *)
Proposition prop_2_4 :
  forall (X Y : Type) (a : X -> Y -> bool),
    searchable Y ->
      (forall x : X, exists y : Y, a x y = true) ->
        exists f : X -> Y, forall x : X, a x (f x) = true.
Proof.
Admitted.

