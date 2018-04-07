Set Universe Polymorphism.

(** * 1.3 Universes and families *)

Notation "'U'" := Type.

(** * 1.4 Dependent function types (Π-types) *)

Notation "A -> B" :=
  (forall _ : A, B) (at level 99, right associativity, B at level 200).

Definition swap {A B C : U} (f : A -> B -> C) : B -> A -> C :=
  fun (b : B) (a : A) => f a b.

(** * 1.12 Identity types *)

Inductive eq {A : U} (x : A) : A -> U :=
    | refl : eq x x.

Arguments refl {A} _.

Notation "x = y" := (eq x y) (at level 70, no associativity).

Ltac refl := apply refl.

(** * 1.5 Product types *)

Inductive prod (A B : U) : U :=
    | pair : A -> B -> prod A B.

Arguments pair {A B} _ _.

Notation "A * B" :=
  (prod A B) (at level 40, left associativity).

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

Definition pr1 {A B : U} (x : A * B) : A :=
match x with
    | (a, _) => a
end.

Definition pr2 {A B : U} (x : A * B) : B :=
match x with
    | (_, b) => b
end.

Definition prod_rec' {A B C : U}
  (f : A -> B -> C) (p : A * B) : C :=
match p with
    | (a, b) => f a b
end.

Definition pr1_rec {A B : U} (x : A * B) : A :=
  prod_rec' (fun a _ => a) x.

Definition pr2_rec {A B : U} (x : A * B) : B :=
  prod_rec' (fun _ b => b) x.

Lemma prod_uniq :
  forall (A B : U) (x : A * B),
    (pr1 x, pr2 x) = x.
Proof.
  destruct x. cbn. refl.
Defined.

Definition prod_ind' {A B : U} {C : A * B -> U}
  (f : forall (a : A) (b : B), C (a, b)) (x : A * B) : C x :=
match x with
    | (a, b) => f a b
end.

(** ** [unit] *)

Inductive unit : U :=
    | tt : unit.

Definition unit_rec' {C : U} (c : C) (u : unit) : C :=
match u with
    | tt => c
end.

Definition unit_ind' {C : unit -> U} (c : C tt) (u : unit) : C u :=
match u with
    | tt => c
end.

Lemma unit_uniq :
  forall u : unit, u = tt.
Proof.
  destruct u. refl.
Defined.

(** * 1.6 Dependent pair types (Σ-types) *)

Inductive sigma {A : U} (B : A -> U) : U :=
    | dpair : forall x : A, B x -> sigma B.

Arguments dpair {A B} _ _.

(*
  Notation "'Σ' x : A , B" := (@sigma A (fun x => B))
  (at level 0, x at level 99, right associativity).
*)

Notation "{ x : A & B }" := (@sigma A (fun x => B))
  (at level 0, x at level 99, right associativity).

Notation "(| x , y , .. , z |)" := (dpair .. (dpair x y) .. z).

Definition pr1' {A : U} {B : A -> U} (x : {a : A & B a}) : A :=
match x with
    | (|a, _|) => a
end.

Definition pr2' {A : U} {B : A -> U} (x : {a : A & B a}) : B (pr1' x) :=
match x with
    | (|_, b|) => b
end.

Definition sigma_rec'
  {A : U} {B : A -> U} {C : U}
  (f : forall x : A, B x -> C) (x : {a : A & B a}) : C :=
match x with
    | (|a, b|) => f a b
end.

Definition sigma_ind'
  {A : U} {B : A -> U} {C : {a : A & B a} -> U}
  (f : forall (a : A) (b : B a), C (|a, b|)) (x : {a : A & B a}) : C x :=
match x with
    | (|a, b|) => f a b
end.

Lemma ac :
  forall (A B : U) (R : A -> B -> U),
    (forall a : A, {b : B & R a b}) ->
      {f : A -> B & forall a : A, R a (f a)}.
Proof.
  intros A B R f.
  apply (dpair (fun a : A => pr1' (f a))).
  apply (fun a : A => pr2' (f a)).
Defined.

Definition Magma : U :=
  {A : U & A -> A -> A}.

Definition PointedMagma : U :=
  {A : U & (A -> A -> A) * A}.

(** * 1.7 Coproduct types *)

Inductive coprod (A B : U) : U :=
    | inl : A -> coprod A B
    | inr : B -> coprod A B.

Arguments inl {A B} _.
Arguments inr {A B} _.

Notation "A + B" := (coprod A B) (at level 50, left associativity).

Definition coprod_rec'
  {A B C : U} (f : A -> C) (g : B -> C) (x : A + B) : C :=
match x with
    | inl a => f a
    | inr b => g b
end.

Definition coprod_ind'
  {A B : U} {C : A + B -> U}
  (f : forall a : A, C (inl a))
  (g : forall b : B, C (inr b))
  (x : A + B) : C x :=
match x with
    | inl a => f a
    | inr b => g b
end.

(** ** [empty] *)

Inductive empty : U := .

Definition empty_rec' {C : U} (x : empty) : C :=
  match x with end.

Definition empty_ind' {C : empty -> U} (x : empty) : C x :=
  match x with end.

(** * 1.8 The type of booleans *)

Inductive bool : U :=
    | true : bool
    | false : bool.

Definition bool_rec'
  {C : U} (c1 c2 : C) (b : bool) : C :=
    if b then c1 else c2.

Definition bool_ind'
  {C : bool -> U} (ct : C true) (cf : C false) (b : bool) : C b :=
match b with
    | true => ct
    | false => cf
end.

Lemma bool_dec :
  forall b : bool,
    (b = true) + (b = false).
Proof.
  destruct b.
    apply (inl (refl true)).
    apply (inr (refl false)).
Defined.

(** We could have done:
    - A + B := {x : bool & bool_rec' A B x}
    - A * B := forall x : bool, bool_rec' A B x
*)

(** * 1.9 The natural numbers *)

Inductive N : U :=
    | O : N
    | S : N -> N.

Notation "0" := O.

Fixpoint double (n : N) : N :=
match n with
    | 0 => 0
    | S n' => S (S (double n'))
end.

Fixpoint add (n m : N) : N :=
match n with
    | 0 => m
    | S n' => S (add n' m)
end.

Fixpoint N_rec' {C : U} (c0 : C) (cS : N -> C -> C) (n : N) : C :=
match n with
    | 0 => c0
    | S n' => cS n' (N_rec' c0 cS n')
end.

Fixpoint N_ind'
  (C : N -> U) (c0 : C 0)
  (cS : forall n : N, C n -> C (S n))
  (n : N) : C n :=
match n with
    | 0 => c0
    | S n' => cS n' (N_ind' C c0 cS n')
end.

Lemma double_rec :
  forall n : N,
    double n =
    N_rec' 0 (fun _ n => S (S n)) n.
Proof.
  apply N_ind'; cbn.
    refl.
    intros n H. rewrite H. refl.
Defined.

Lemma add_rec :
  forall n m : N,
    add n m =
    N_rec' (fun n => n) (fun _ f n => S (f n)) n m.
Proof.
  apply
    (N_ind'
      (fun n : N => forall m : N,
        add n m =
        N_rec' (fun n : N => n) (fun _ f n => S (f n)) n m));
  cbn.
    refl.
    intros n H m. rewrite H. refl.
Defined.

Lemma assoc :
  forall i j k : N,
    add i (add j k) = add (add i j) k.
Proof.
  apply
    (N_ind'
      (fun i : N =>
        forall j k : N, add i (add j k) = add (add i j) k));
  cbn.
    intros. refl.
    intros n H j k. rewrite H. refl.
Defined.

(** * 1.11 Propositions as types *)

Definition not (A : U) := A -> empty.

Notation "~ A " := (not A) (at level 75, right associativity).

Lemma and_not :
  forall A B : U,
    (~ A) * (~ B) -> ~ (A + B).
Proof.
  destruct 1 as [na nb]. destruct 1 as [a | b].
    apply na, a.
    apply nb, b.
Defined.

Definition le (n m : N) : U :=
  {k : N & add n k = m}.

Definition lt (n m : N) : U :=
  {k : N & add n (S k) = m}.

(** * 1.12 Identity types *)

Definition indiscernability
  {A : U} {C : A -> U} {x y : A} (p : x = y) (cx : C x) : C y :=
match p with
    | refl _ => cx
end.

Definition path_ind
  {A : U} {C : forall x y : A, x = y -> U}
  (c : forall x : A, C x x (refl x)) (x y : A) (p : x = y) : C x y p :=
match p with
    | refl _ => c x
end.

Notation "'J'" := path_ind (only parsing).

Definition based_path_ind
  {A : U} {a : A} {C : forall x : A, a = x -> U}
  (c : C a (refl a)) (x : A) (p : a = x) : C x p :=
match p with
    | refl _ => c
end.

Lemma mystery :
  forall (A : U) (x y : A) (p : x = y),
    @dpair _ (fun x : A => {y : A & x = y}) x (dpair y p) =
    @dpair _ (fun x : A => {y : A & x = y}) x (dpair x (refl x)).
Proof.
  destruct p. refl.
Defined.

Notation "x <> y" := (~ x = y) (at level 50).

(** Chapter 2 *)

(** * 2.1 Types are higher groupoids *)

Definition inv {A : U} {x y : A} (p : x = y) : y = x :=
match p with
    | refl _ => refl x
end.

Definition cat {A : U} {x y z : A} (p : x = y) (q : y = z) : x = z :=
match p, q with
    | refl _, refl _ => refl x
end.

(* Lemma 2.1.4 *)
Lemma cat_refl_l :
  forall (A : U) (x y : A) (p : x = y),
    cat (refl x) p = p.
Proof.
  destruct p. refl.
Defined.

Lemma cat_refl_r :
  forall (A : U) (x y : A) (p : x = y),
    cat p (refl y) = p.
Proof.
  destruct p. refl.
Defined.

Lemma cat_inv_l :
  forall (A : U) (x y : A) (p : x = y),
    cat (inv p) p = refl y.
Proof.
  destruct p. refl.
Defined.

Lemma cat_inv_r :
  forall (A : U) (x y : A) (p : x = y),
    cat p (inv p) = refl x.
Proof.
  destruct p. refl.
Defined.

Lemma inv_inv :
  forall (A : U) (x y : A) (p : x = y),
    inv (inv p) = p.
Proof.
  destruct p. refl.
Defined.

Lemma cat_assoc :
  forall (A : U) (x y z w : A) (p : x = y) (q : y = z) (r : z = w),
    cat p (cat q r) = cat (cat p q) r.
Proof.
  destruct p, q, r. cbn. refl.
Defined.

(** Eckmann-Hilton omitted *)

(*Record Pointed : U :=
{
    carrier : U;
    point : carrier;
}.

Instance loopspace Pointed : d :=
{
    carrier := a = a;
    point := refl a;
}.*)

Definition Pointed : U := {A : U & A}.

Notation "U*" := Pointed.

Definition loopspace (A : U*) : U* :=
match A with
    | (| _, a |) => (| a = a, refl a |)
end.

Fixpoint nfold_loopspace (n : N) (A : U*) : U* :=
match n with
    | 0 => A
    | S n' => nfold_loopspace n' (loopspace A)
end.

(** * 2.2 Functions are functors *)

Definition ap {A B : U} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
match p with
    | refl _ => refl (f x)
end.

(* Lemma 2.2.2 *)

Lemma ap_cat :
  forall (A B : U) (f : A -> B) (x y z : A) (p : x = y) (q : y = z),
    ap f (cat p q) = cat (ap f p) (ap f q).
Proof.
  destruct p, q. cbn. refl.
Defined.

Lemma ap_inv :
  forall (A B : U) (f : A -> B) (x y : A) (p : x = y),
    ap f (inv p) = inv (ap f p).
Proof.
  destruct p. cbn. refl.
Defined.

Lemma ap_ap
  forall (A B C : U) (f : A -> B) (x y : A) (p : x = y),
    ap g (ap f p) = ap (comp g f) p.
Proof.
  destruct p, q. cbn. refl.
Defined.