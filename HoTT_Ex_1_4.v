(* Ex. 1.4 *)
Fixpoint iter (C : Type) (c0 : C) (cs : C -> C) (n : nat) : C :=
match n with
    | 0 => c0
    | S n' => cs (iter C c0 cs n')
end.

Definition rec (C : Type) (c0 : C) (cs : nat -> C -> C) (n : nat) : C :=
  iter
    (nat -> C -> C)
    (fun _ _ => c0)
    (fun f k c => cs (pred k) (f (pred k) c))
    n
    n
    c0.

Theorem rec_spec_0 :
  forall (C : Type) (c0 : C) (cs : nat -> C -> C),
    rec C c0 cs 0 = c0.
Proof.
  reflexivity.
Qed.

Theorem rec_spec_1 :
  forall (C : Type) (c0 : C) (cs : nat -> C -> C) (n : nat),
    rec C c0 cs (S n) = cs n (rec C c0 cs n).
Proof.
  intros. unfold rec. cbn.
  reflexivity.
Qed.

(* Ex. 1.9 *)
Inductive Fin : nat -> Type :=
    | Fin_1 : Fin 1
    | Fin_SS : forall n : nat, Fin (S n) -> Fin (S (S n)).

Fixpoint fmax (n : nat) : Fin (S n) :=
match n with
    | 0 => Fin_1
    | S n' => Fin_SS n' (fmax n')
end.

(* Ex. 1.10 *)
Definition ack : nat -> nat -> nat :=
  rec
    (nat -> nat)
    S
    (fun (m : nat) (f : nat -> nat) =>
      rec
        nat
        (f 1)
        (fun n r : nat => f r)).

Fixpoint ack' (m : nat) : nat -> nat :=
match m with
    | 0 => S
    | S m' => fix f (n : nat) : nat :=
        match n with
            | 0 => ack' m' 1
            | S n' => ack' m' (f n')
        end
end.

Goal forall m n : nat, ack m n = ack' m n.
Proof.
  induction m as [| m']; cbn.
    trivial.
    induction n as [| n']; cbn.
      rewrite <- IHm'. reflexivity.
      rewrite <- IHm', <- IHn'. reflexivity.
Qed.

(* Ex. 1.11 *)
Goal forall A : Prop, ~ ~ ~ A -> ~ A.
Proof.
  intros. intro. apply H. intro. apply H1. assumption.
Qed.

Definition sum' A B := {b : bool & if b then A else B}.

Definition inl' {A B : Type} (a : A) : sum' A B := existT _ true a.
Definition inr' {A B : Type} (b : B) : sum' A B := existT _ false b.

Check sum_ind.
Definition sum'_ind :
  forall (A B : Type) (P : sum' A B -> Prop),
    (forall a : A, P (inl' a)) ->
    (forall b : B, P (inr' b)) ->
      forall p : sum' A B, P p.
Proof.
  destruct p. destruct x.
    apply H.
    apply H0.
Defined.

Print sum'_ind.
