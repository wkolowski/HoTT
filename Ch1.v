Notation "A -> B" :=
  (forall _ : A, B) (at level 99, right associativity, B at level 200).

Inductive prod (A B : Type) : Type :=
    | pair : A -> B -> prod A B.

Arguments pair {A B} _ _.

Notation "A * B" :=
  (prod A B) (at level 40, left associativity).

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

Inductive unit : Type :=
    | tt : unit.

Definition pr1 {A B : Type} (x : A * B) : A :=
match x with
    | (a, _) => a
end.

Definition pr2 {A B : Type} (x : A * B) : B :=
match x with
    | (_, b) => b
end.

Inductive eq {A : Type} (x : A) : A -> Type :=
    | refl : eq x x.

Arguments refl {A} _.

Notation "x = y" := (eq x y) (at level 70, no associativity).

Ltac refl := apply refl.

Lemma prod_uniq :
  forall (A B : Type) (x : A * B),
    (pr1 x, pr2 x) = x.
Proof.
  destruct x. cbn. refl.
Defined.

Lemma unit_uniq :
  forall u : unit, u = tt.
Proof.
  destruct u. refl.
Defined.

Inductive sigma {A : Type} (B : A -> Type) : Type :=
    | dpair : forall x : A, B x -> sigma B.

Arguments dpair {A B} _ _.

(*
  Notation "'Σ' x : A , B" := (@sigma A (fun x => B))
  (at level 0, x at level 99, right associativity).
*)

Notation "{ x : A & B }" := (@sigma A (fun x => B))
  (at level 0, x at level 99, right associativity).

Check forall A : Type, {x : A & x = x}.