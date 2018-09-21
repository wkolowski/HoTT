(* Required in 8.8.1 to make Ltac work with the -noinit option. *)
Declare ML Module "ltac_plugin".
Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

(** Chapter 1 *)

(** * 1.3 Universes and families *)

Definition U := Type.

(*Notation "'U'" := Type.
*)

(** * 1.4 Dependent function types (Π-types) *)

Notation "A -> B" :=
  (forall _ : A, B) (at level 99, right associativity, B at level 200).

Definition id {A : U} (x : A) : A := x.

Definition swap {A B C : U} (f : A -> B -> C) : B -> A -> C :=
  fun (b : B) (a : A) => f a b.

(** * 1.12 Identity types *)

Inductive eq {A : U} (x : A) : A -> U :=
    | refl : eq x x.

Arguments refl {A} _.

Notation "x = y" := (eq x y) (at level 70, no associativity).

Ltac refl := intros; apply refl.

(** * 1.5 Product types *)

Inductive prod (A B : U) : U :=
    | pair : A -> B -> prod A B.

Arguments pair {A B} _ _.

Notation "A * B" :=
  (prod A B) (at level 40, right associativity).

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

Ltac hsplit :=
match goal with
    | |- ?A * ?B =>
        assert (a : A); [idtac |  assert (b : B); [idtac | apply (a, b)]]
end.

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

(*
Definition le (n m : N) : U :=
  {k : N & add n k = m}.

Definition lt (n m : N) : U :=
  {k : N & add n (S k) = m}.
*)

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

(** * Exercises *)

(** **** Ex. 1.1 *)

Definition comp {A B C : U} (f : A -> B) (g : B -> C) : A -> C :=
  fun x : A => g (f x).

Lemma comp_assoc :
  forall (A B C D : U) (f : A -> B) (g : B -> C) (h : C -> D),
    comp (comp f g) h = comp f (comp g h).
Proof. refl. Defined.

(** **** Ex. 1.2 *)

Definition prod_rec''
  (A B P : U) (f : A -> B -> P) (p : A * B) : P := f (pr1 p) (pr2 p).

Lemma prod_rec''_computation :
  forall (A B P : U) (f : A -> B -> P) (a : A) (b : B),
    prod_rec'' A B P f (a, b) = f a b.
Proof. refl. Defined.

Definition sigma_rec''
  (A : U) (B : A -> U) (P : U) (f : forall a : A, B a -> P)
  (p : {a : A & B a}) : P := f (pr1' p) (pr2' p).

Lemma sigma_rec''_computation :
  forall
    (A : U) (B : A -> U) (P : U)
    (f : forall a : A, B a -> P) (a : A) (b : B a),
      sigma_rec'' A B P f (| a, b |) = f a b.
Proof. refl. Defined.

(** **** Ex. 1.3 *)

Definition prod_ind''
  (A B : U) (P : A * B -> U) (f : forall (a : A) (b : B), P (a, b))
  (p : A * B) : P p.
Proof.
  rewrite <- prod_uniq. apply f.
Defined.

Lemma prod_ind''_computation :
  forall (A B : U) (P : A * B -> U) (f : forall (a : A) (b : B), P (a, b))
    (a : A) (b : B), prod_ind'' A B P f (a, b) = f a b.
Proof. refl. Defined.

Lemma sigma_uniq' :
  forall (A : U) (B : A -> U) (p : {a : A & B a}),
    p = (| pr1' p, pr2' p |).
Proof.
  destruct p. cbn. refl.
Defined.

Lemma sigma_ind''
  (A : U) (B : A -> U) (P : {a : A & B a} -> U)
  (f : forall (a : A) (b : B a), P (| a, b |)) (p : {a : A & B a}) : P p.
Proof.
  rewrite sigma_uniq'. apply f.
Defined.

Lemma sigma_ind''_computation :
  forall
    (A : U) (B : A -> U) (P : sigma B -> U)
    (f : forall (a : A) (b : B a), P (| a, b |))
    (a : A) (b : B a),
      sigma_ind'' A B P f (| a, b |) = f a b.
Proof. refl. Defined.

(** Looks like concepts from chapter 2 are NOT needed. *)

(** **** Ex. 1.4 *)
Fixpoint iter (C : U) (c0 : C) (cs : C -> C) (n : N) : C :=
match n with
    | 0 => c0
    | S n' => cs (iter C c0 cs n')
end.

Definition pred (n : N) : N :=
match n with
    | 0 => 0
    | S n' => n'
end.

Definition rec (C : U) (c0 : C) (cs : N -> C -> C) (n : N) : C :=
  iter
    (N -> C -> C)
    (fun _ _ => c0)
    (fun f k c => cs (pred k) (f (pred k) c))
    n
    n
    c0.

Lemma rec_spec_0 :
  forall (C : U) (c0 : C) (cs : N -> C -> C),
    rec C c0 cs 0 = c0.
Proof.
  reflexivity.
Defined.

Lemma rec_spec_1 :
  forall (C : U) (c0 : C) (cs : N -> C -> C) (n : N),
    rec C c0 cs (S n) = cs n (rec C c0 cs n).
Proof.
  intros. unfold rec. cbn.
  reflexivity.
Defined.

(** **** Ex. 1.5 *)

Definition coprod' (A B : U) := {b : bool & if b then A else B}.
Definition inl' {A B : U} (a : A) : coprod' A B := (| true, a |).
Definition inr' {A B : U} (b : B) : coprod' A B := (| false, b |).

Definition coprod'_ind
  {A B : U} {P : coprod' A B -> U}
  (f : forall a : A, P (| true, a |)) (g : forall b : B, P (| false, b |))
  (p : coprod' A B) : P p.
Proof.
  destruct p as [[]]; [apply f | apply g].
Defined.

Lemma coprod'_ind_inl' :
  forall
    (A B : U) (P : coprod' A B -> U)
    (f : forall a : A, P (| true, a |)) (g : forall b : B, P (| false, b |))
    (a : A),
      coprod'_ind f g (inl' a) = f a.
Proof. refl. Defined.

Lemma coprod'_ind_inr' :
  forall
    (A B : U) (P : coprod' A B -> U)
    (f : forall a : A, P (| true, a |)) (g : forall b : B, P (| false, b |))
    (b : B),
      coprod'_ind f g (inr' b) = g b.
Proof. refl. Defined.

(** **** Ex. 1.6 MOVED *)

(** **** Ex. 1.7 *)

Definition eq_ind1_type : U :=
  forall (A : U) (C : forall x y : A, x = y -> U),
    (forall x : A, C x x (refl x)) ->
      forall (x y : A) (p : x = y), C x y p.

Definition eq_ind2_type : U :=
  forall (A : U) (a : A) (C : forall x : A, a = x -> U),
    C a (refl a) -> forall (x : A) (p : a = x), C x p.

Lemma to_1_2 :
  eq_ind1_type -> eq_ind2_type.
Proof.
  unfold eq_ind1_type, eq_ind2_type. intros path_ind **.
  apply (path_ind A (fun _ _ _ => C x p)
                  (fun _ => match p with refl _ => X end) a x p).
Defined.

Lemma to_2_1 :
  eq_ind2_type -> eq_ind1_type.
Proof.
  unfold eq_ind1_type, eq_ind2_type. intros based_path_ind **.
  apply (based_path_ind A x (fun y p => C x y p) (X x) y p).
Defined.

(** **** Ex. 1.16 *)

Lemma add_comm :
  forall n m : N, add n m = add m n.
Proof.
  induction n as [| n']; cbn; intros.
    induction m as [| m']; cbn.
      refl.
      rewrite <- IHm'. refl.
    rewrite IHn'. induction m as [| m']; cbn.
      refl.
      rewrite <- IHm'. refl.
Defined.

(** **** Ex. 1.8 TODO *)

Definition mul (n : N) : N -> N :=
  N_rect (fun _ => N) 0 (fun m r => add n r).

(*
Definition mul : N -> N -> N :=
  N_rect (fun _ => N -> N) (fun _ => 0) (fun n r => fun m => add n (r m)).
*)

Lemma add_0_r :
  forall n : N, add n 0 = n.
Proof.
  induction n as [| n']; cbn.
    refl.
    rewrite IHn'. refl.
Defined.

Lemma add_assoc :
  forall a b c : N,
    add (add a b) c = add a (add b c).
Proof.
  induction a as [| a']; cbn; intros.
    refl.
    rewrite IHa'. refl.
Defined.

Lemma mul_0_l :
  forall n : N, mul 0 n = 0.
Proof.
  induction n as [| n']; cbn.
    refl.
    rewrite IHn'. refl.
Defined.

Lemma mul_0_r :
  forall n : N, mul n 0 = 0.
Proof. refl. Defined.

Lemma mul_comm :
  forall n m : N, mul n m = mul m n.
Proof.
  intros. revert n.
  induction m as [| m']; cbn; intros.
    rewrite mul_0_l. refl.
    induction n as [| n']; cbn.
      rewrite mul_0_l. refl.
      rewrite IHm', <- IHn', IHm'. cbn. rewrite <- !add_assoc.
        rewrite (add_comm n' m'). refl.
Defined.

Lemma mul_add_l :
  forall a b c : N,
    mul a (add b c) = add (mul a b) (mul a c).
Proof.
  intros a b c. revert a c.
  induction b as [| b']; cbn; intros.
    refl.
    rewrite IHb', add_assoc. refl.
Defined.

Lemma mul_add_r :
  forall a b c : N,
    mul (add a b) c = add (mul a c) (mul b c).
Proof.
  intros. rewrite mul_comm, mul_add_l, (mul_comm c a), (mul_comm c b). refl.
Defined.

Lemma mul_assoc :
  forall a b c : N, mul (mul a b) c = mul a (mul b c).
Proof.
  intros. revert a b.
  induction c as [| c']; cbn; intros.
    refl.
    rewrite IHc'. rewrite mul_add_l. refl.
Defined.

(*
(R, +) is a commutative monoid with identity element 0:
(a + b) + c = a + (b + c)
0 + a = a + 0 = a
a + b = b + a
(R, ⋅) is a monoid with identity element 1:
(a⋅b)⋅c = a⋅(b⋅c)
1⋅a = a⋅1 = a
Multiplication left and right distributes over addition:
a⋅(b + c) = (a⋅b) + (a⋅c)
(a + b)⋅c = (a⋅c) + (b⋅c)
Multiplication by 0 annihilates R:
0⋅a = a⋅0 = 0
*)

(** **** Ex. 1.9 *)
Inductive Fin : N -> U :=
    | Fin_1 : Fin (S 0)
    | Fin_SS : forall n : N, Fin (S n) -> Fin (S (S n)).

Fixpoint fmax (n : N) : Fin (S n) :=
match n with
    | 0 => Fin_1
    | S n' => Fin_SS n' (fmax n')
end.

Notation "1" := (S 0).

(** **** Ex. 1.10 *)
Definition ack : N -> N -> N :=
  rec
    (N -> N)
    S
    (fun (m : N) (f : N -> N) =>
      rec
        N
        (f 1)
        (fun n r : N => f r)).

Fixpoint ack' (m : N) : N -> N :=
match m with
    | 0 => S
    | S m' => fix f (n : N) : N :=
        match n with
            | 0 => ack' m' 1
            | S n' => ack' m' (f n')
        end
end.

Lemma ex_1_10 :
  forall m n : N, ack m n = ack' m n.
Proof.
  induction m as [| m']; cbn.
    refl.
    induction n as [| n']; cbn.
      rewrite <- IHm'. refl.
      rewrite <- IHm', <- IHn'. refl.
Defined.

(** **** Ex. 1.11 *)
Lemma ex_1_11 :
  forall A : Prop, ~ ~ ~ A -> ~ A.
Proof.
  intros. intro. apply X. intro. apply X0. assumption.
Defined.

(** **** Ex. 1.12 *)

Lemma ex_1_12_1 :
  forall A B : U, A -> B -> A.
Proof.
  intros A B a b. assumption.
Defined.

Lemma ex_1_12_2 :
  forall A B : U, A -> ~ ~ A.
Proof.
  intros A B a f. apply f. assumption.
Defined.

Lemma ex_1_12_3 :
  forall A B : U, ((~ A) + ~ B) ->  ~ (A * B).
Proof.
  intros A B [f | f] [a b]; contradiction.
Defined.

(** **** Ex. 1.13 *)

Lemma ex_1_13 :
  forall P : U, ~ ~ (P + ~ P).
Proof.
  intros P f. apply f. right. intro p. apply f. left. assumption.
Defined.

(** **** Ex. 1.14 MOVED *)

(** **** Ex. 1.15 *)

Definition indiscernability_type : U :=
  forall (A : U) (C : A -> U) (x y : A), x = y -> C x -> C y.

Lemma ex_1_15 :
  eq_ind1_type -> indiscernability_type.
Proof.
  unfold eq_ind1_type, indiscernability_type.
  intros path_ind * p c.
  apply (path_ind A (fun _ _ _ => C y)
                       (fun _ => match p with | refl _ => c end)
                       _ _ p).
Defined.

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

(*
Definition cat {A : U} {x y : A} (p : x = y) {z : A} (q : y = z) : x = z :=
match p, q with
    | refl _, refl _ => refl x
end.
*)

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

(** Eckmann-Hilton omitted TODO *)

(*
Class Pointed : U :=
{
    carrier : U;
    basepoint : carrier;
}.

Instance loopspace (A : Pointed) : Pointed :=
{
    carrier := @basepoint A = @basepoint A;
    basepoint := refl (@basepoint A);
}.

Definition Pointed : U := {A : U & A}.

Definition loopspace (A : Pointed) : Pointed :=
match A with
    | (| _, a |) => (| a = a, refl a |)
end.
*)

Definition loopspace (A : U) (a : A) : U := a = a.

Fixpoint nfold_loopspace (n : N) (A : U) (a : A) : U :=
match n with
    | 0 => loopspace A a
    | S n' => nfold_loopspace n' (loopspace A a) (refl a)
end.

Definition loopspace2 (A : U) (a : A) : U := refl a = refl a.

Infix "^" := cat (at level 60, right associativity).

Definition whisker_l
  {A : U} {a b c : A} {r s : b = c} (q : a = b) (beta : r = s)
  : cat q r = cat q s.
Proof.
  destruct q.
  exact ((cat_refl_l _ _ _ r) ^ beta ^ inv (cat_refl_l _ _ _ s)).
Defined.

Definition whisker_r
  {A : U} {a b c : A} {p q : a = b} (alfa : p = q) (r : b = c)
  : cat p r = cat q r.
Proof.
  destruct r.
  exact ((cat_refl_r _ _ _ p) ^ alfa ^ inv (cat_refl_r _ _ _ q)).
Defined.

Definition horizontal_comp
  {A : U} {a b c : A} {p q : a = b} {r s : b = c}
  (alfa : p = q) (beta : r = s)
  : cat p r = cat q s :=
    whisker_r alfa r ^ whisker_l q beta.

Definition horizontal_comp'
  {A : U} {a b c : A} {p q : a = b} {r s : b = c}
  (alfa : p = q) (beta : r = s)
  : cat p r = cat q s :=
    whisker_l p beta ^ whisker_r alfa s.

Lemma wut :
  forall (A : U) (x y : A) (p q : x = y) (alfa : p = q),
    match alfa in (_ = q) return (p = q) with
        | refl _ => refl p
    end
    = alfa.
Proof.
  destruct alfa. refl.
Defined.

Lemma horizontal_comp_spec :
  forall
    {A : U} {a : A} (alfa beta : refl a = refl a),
      horizontal_comp alfa beta = alfa ^ beta.
Proof.
  intros. unfold horizontal_comp, whisker_l, whisker_r. simpl.
  rewrite !cat_refl_r, !wut. refl.
Defined.

Lemma horizontal_comp'_spec :
  forall
    {A : U} {a : A} (alfa beta : refl a = refl a),
      horizontal_comp' alfa beta = beta ^ alfa.
Proof.
  intros. unfold horizontal_comp', whisker_l, whisker_r. simpl.
  rewrite !cat_refl_r, !wut. refl.
Defined.

Lemma horizontal_comps :
  forall
    {A : U} {a b c : A} {p q : a = b} {r s : b = c}
    (alfa : p = q) (beta : r = s),
      horizontal_comp alfa beta = horizontal_comp' alfa beta.
Proof.
  destruct alfa, beta. destruct p, r. compute. refl.
Defined.

Lemma Eckmann_Hiltron :
  forall {A : U} {a : A} (alfa beta : refl a = refl a),
    alfa ^ beta = beta ^ alfa.
Proof.
  intros.
  rewrite <- horizontal_comp_spec.
  rewrite <- horizontal_comp'_spec.
  rewrite horizontal_comps. refl.
Defined.

(* TODO *)
Lemma whisker_l_cat :
  forall
    {A : U} {a b c : A} {p : a = a} {q : a = a} (alfa : p = q), U.
Proof.
  intros.
Check      whisker_r alfa (cat p q).

Check whisker_r (whisker_r alfa q) p.
Abort.



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

Lemma ap_ap :
  forall (A B C : U) (f : A -> B) (g : B -> C) (x y : A) (p : x = y),
    ap g (ap f p) = ap (comp f g) p.
Proof.
  destruct p. refl.
Defined.

Lemma ap_id :
  forall (A : U) (x y : A) (p : x = y),
    ap id p = p.
Proof.
  destruct p. refl.
Defined.

(** * 2.3 Type families are fibrations *)

(* Lemma 2.3.1 *)
Definition transport {A : U} (P : A -> U) {x y : A}
  (p : x = y) : P x -> P y :=
match p with
    | refl _ => id
end.

Notation "p *" := (transport p) (at level 50, only parsing).

(** Path lifting omitted. *)

(* Lemma 2.3.4 *)
Definition apd
  {A : U} {P : A -> U} (f : forall x : A, P x) {x y : A} (p : x = y)
  : transport P p (f x) = (f y) :=
match p with
    | refl _ => refl (f x)
end.

(* Lemma 2.3.5 *)
Lemma transportconst {A B : U} {x y : A} (p : x = y) (b : B) :
  @transport A (fun _ => B) x y p b = b.
Proof.
  destruct p. cbn. refl.
Defined.

(* Lemma 2.3.8 *)
Lemma apd_transportconst_ap :
  forall (A B : U) (f : A -> B) (x y : A) (p : x = y),
    apd f p = cat (transportconst p (f x)) (ap f p).
Proof.
  destruct p. cbn. refl.
Defined.

(* Lemma 2.3.9 *)
Lemma transport_cat :
  forall (A : U) (P : A -> U) (x y z : A) (p : x = y) (q : y = z) (u : P x),
    transport P q (transport P p u) = transport P (cat p q) u.
Proof.
  destruct p, q. cbn. refl.
Defined.

(* Lemma 2.3.10 *)
Lemma transport_ap :
  forall (A B : U) (P : B -> U) (f : A -> B)
    (x y : A) (p : x = y) (u : P (f x)),
      @transport A (comp f P) x y p u = transport P (ap f p) u.
Proof.
  destruct p. cbn. refl.
Defined.

(* Lemma 2.3.11 *)
Lemma transport_family :
  forall (A : U) (P Q : A -> U) (f : forall x : A, P x -> Q x)
    (x y : A) (p : x = y) (u : P x),
      transport Q p (f x u) = f y (transport P p u).
Proof.
  destruct p. cbn. refl.
Defined.

(** * 2.4 Homotopies and equivalences *)

Definition homotopy {A : U} {P : A -> U} (f g : forall x : A, P x) : U :=
  forall x : A, f x = g x.

(* Lemma 2.4.2 *)
Lemma homotopy_refl :
  forall (A : U) (P : A -> U) (f : forall x : A, P x),
    homotopy f f.
Proof.
  unfold homotopy. refl.
Defined.

Lemma homotopy_sym :
  forall (A : U) (P : A -> U) (f g : forall x : A, P x),
    homotopy f g -> homotopy g f.
Proof.
  unfold homotopy. intros. rewrite X. refl.
Defined.

Lemma homotopy_trans :
  forall (A : U) (P : A -> U) (f g h : forall x : A, P x),
    homotopy f g -> homotopy g h -> homotopy f h.
Proof.
  unfold homotopy. intros. rewrite X, X0. refl.
Defined.

(* Lemma 2.4.3 *)
Lemma homotopy_natural :
  forall (A B : U) (f g : A -> B) (H : homotopy f g) (x y : A) (p : x = y),
    cat (H x) (ap g p) = cat (ap f p) (H y).
Proof.
  unfold homotopy. destruct p. cbn. destruct (H x). cbn. refl.
Defined.

Lemma ap_refl :
  forall (A B : U) (f : A -> B) (x : A),
    ap f (refl x) = refl (f x).
Proof. refl. Defined.

(* Corollary 2.4.4 *)
Lemma homotopy_id :
  forall (A : U) (f : A -> A) (H : homotopy f id) (x : A),
    H (f x) = ap f (H x).
Proof.
  intros.
  assert (cat (cat (H (f x)) (H x)) (inv (H x)) =
          cat (cat (ap f (H x)) (H x)) (inv (H x))).
    pose (e := homotopy_natural A A f id H (f x) x (H x)).
      rewrite ap_id in e. rewrite e. refl.
    rewrite <- !cat_assoc, !cat_inv_r, !cat_refl_r in X. apply X.
Defined.

Definition qinv {A B : U} (f : A -> B) : U :=
  {g : B -> A & homotopy (comp g f) id * homotopy (comp f g) id}.

Lemma qinv_transport :
  forall (A : U) (P : A -> U) (x y : A) (p : x = y),
    qinv (@transport A P x y p).
Proof.
  intros. eapply (| @transport A P y x (inv p), _ |).
Unshelve.
  cbn. hsplit.
    destruct p. compute. refl.
    destruct p. compute. refl.
Defined.

Definition isequiv {A B : U} (f : A -> B) : U :=
  {g : B -> A & homotopy (comp g f) (@id B)} *
  {h : B -> A & homotopy (comp f h) (@id A)}.

Ltac ex :=
match goal with
    | |- {a : ?A & ?B} =>
        let a := fresh "a" in
        assert (a : A); [idtac | assert (b : B); [idtac | apply (| a, b |)]]
end.

Lemma qinv_isequiv :
  forall (A B : U) (f : A -> B),
    qinv f -> isequiv f.
Proof.
  destruct 1 as [g [α β]].
  unfold isequiv. hsplit.
    apply (| g, α |).
    apply (| g, β |).
Defined.

Lemma isequiv_qinv :
  forall (A B : U) (f : A -> B),
    isequiv f -> qinv f.
Proof.
  destruct 1 as [[g α] [h β]].
  unfold qinv.
  eapply (| comp g (comp f h), _ |).
Unshelve.
  cbn. hsplit; compute in *; intros.
    rewrite β, α. refl.
    rewrite α, β. refl.
Defined.

Definition equiv (A B : U) : U :=
  {f : A -> B & isequiv f}.

Notation "A ~ B" := (equiv A B) (at level 50).

(* Lemma 2.4.12 *)
Lemma equiv_refl :
  forall A : U, equiv A A.
Proof.
  unfold equiv. intros.
  eapply (| id, _ |).
Unshelve.
  cbn. apply qinv_isequiv. compute. eapply (| id, _ |).
Unshelve.
  compute. hsplit; refl.
Defined.

Lemma equiv_sym :
  forall A B : U, equiv A B -> equiv B A.
Proof.
  unfold equiv. destruct 1 as [f H].
  apply isequiv_qinv in H. destruct H as [g [α β]].
  eapply (| g, _ |).
Unshelve.
  cbn. apply qinv_isequiv. eapply (| f, _ |).
Unshelve.
  compute in *. hsplit; intros; rewrite ?α, ?β; refl.
Defined.

Lemma equiv_trans :
  forall A B C : U, equiv A B -> equiv B C -> equiv A C.
Proof.
  unfold equiv. destruct 1 as [f Hf], 1 as [g Hg].
  apply isequiv_qinv in Hf; apply isequiv_qinv in Hg.
  destruct Hf as [f' [Hf1 Hf2]], Hg as [g' [Hg1 Hg2]].
  eapply (| comp f g, _ |).
Unshelve.
  cbn. apply qinv_isequiv. eapply (| comp g' f', _ |).
Unshelve.
  compute in *. hsplit; intros.
    rewrite Hf1, Hg1. refl.
    rewrite Hg2, Hf2. refl.
Restart.
  unfold equiv.
  destruct 1 as (f & (f1 & Hf1) & (f2 & Hf2)).
  destruct 1 as (g & (g1 & Hg1) & (g2 & Hg2)).
  compute in *. exists (comp f g). split.
    exists (comp g1 f1). intro. compute.
      specialize (Hf1 (g1 x)). apply (ap g) in Hf1.
        exact (cat Hf1 (Hg1 x)).
    exists (comp g2 f2). compute. intro.
      specialize (Hg2 (f x)). apply (ap f2) in Hg2.
        exact (cat Hg2 (Hf2 x)).
Defined.

Definition prod_eq_intro
  {A B : U} {x y : A * B} (pq : (pr1 x = pr1 y) * (pr2 x = pr2 y)) : x = y.
Proof.
  destruct x, y; cbn in *. destruct pq as [[] []]. refl.
Defined.

Notation "'pair=' p q" := (prod_eq_intro p q) (at level 50).

(* In the book, elimination rules for products are [ap pr1] and [ap pr2]. *)
Definition prod_eq_elim
  {A B : U} {x y : A * B} (p : x = y) : (pr1 x = pr1 y) * (pr2 x = pr2 y) :=
    (ap pr1 p, ap pr2 p).

Lemma prod_eq_comp_1 :
  forall (A B : U) (x y : A * B) (p : pr1 x = pr1 y) (q : pr2 x = pr2 y),
    ap pr1 (prod_eq_intro (p, q)) = p.
Proof.
  destruct x, y. cbn. destruct p, q. compute. refl.
Defined.

Lemma prod_eq_comp_2 :
  forall (A B : U) (x y : A * B) (p : pr1 x = pr1 y) (q : pr2 x = pr2 y),
    ap pr2 (prod_eq_intro (p, q)) = q.
Proof.
  destruct x, y. cbn. destruct p, q. compute. refl.
Defined.

Lemma prod_eq_uniq :
  forall (A B : U) (x y : A * B) (p : x = y),
    p = prod_eq_intro (ap pr1 p, ap pr2 p).
Proof.
  destruct p, x. cbn. refl.
Defined.

(* Theorem 2.6.2 *)
Lemma prod_eq_intro_isequiv :
  forall (A B : U) (x y : A * B),
    isequiv (@prod_eq_intro A B x y).
Proof.
  intros. apply qinv_isequiv. unfold qinv.
  eapply (| fun p => (ap pr1 p, ap pr2 p), _ |).
Unshelve.
  cbn. hsplit.
    unfold homotopy. intros H. destruct H, x. cbn. refl.
    unfold homotopy. intros H. destruct x, y. cbn in *.
      destruct H as [[] []]. compute. refl.
Defined.

(* Characterization of paths between pairs. *)
Lemma refl_prod_eq :
  forall (A B : U) (x : A * B),
    refl x = prod_eq_intro (refl (pr1 x), refl (pr2 x)).
Proof.
  destruct x. cbn. refl.
Defined.

Lemma inv_prod_eq :
  forall (A B : U) (x y : A * B) (p : x = y),
    inv p = prod_eq_intro (inv (ap pr1 p), inv (ap pr2 p)).
Proof.
  destruct p, x. cbn. refl.
Defined.

Lemma cat_prod_eq :
  forall (A B : U) (x y z : A * B) (p : x = y) (q : y = z),
    cat p q =
    prod_eq_intro (cat (ap pr1 p) (ap pr1 q), cat (ap pr2 p) (ap pr2 q)).
Proof.
  destruct p, q, x. cbn. refl.
Defined.

(* Theorem 2.6.4 *)
Theorem transport_prod :
  forall (Z : U) (A B : Z -> U) (z z' : Z) (p : z = z') (x : A z * B z),
    @transport _ (fun z : Z => A z * B z) _ _ p x =
    (transport A p (pr1 x), transport B p (pr2 x)).
Proof.
  destruct p, x. cbn. refl.
Defined.

Definition fpair {A A' B B'} (f : A -> A') (g : B -> B')
  : A * B -> A' * B' :=
    fun x => (f (pr1 x), g (pr2 x)).

(* Theorem 2.6.5 *)
Theorem ap_prod_eq_intro :
  forall (A A' B B' : U) (x y : A * B)
  (p : pr1 x = pr1 y) (q : pr2 x = pr2 y)
  (f : A -> A') (g : B -> B'),
    ap (fpair f g) (prod_eq_intro (p, q)) =
    @prod_eq_intro _ _ (fpair f g x) (fpair f g y) (ap f p, ap g q).
Proof.
  destruct x, y. cbn. destruct p, q. compute. refl.
Defined.

(** * 2.7 Σ-types *)

Definition sigma_eq_intro
  {A : U} {B : A -> U} {x y : {x : A & B x}}
  (p : {p : pr1' x = pr1' y & transport B p (pr2' x) = pr2' y}) : x = y.
Proof.
  destruct x as [x b1], y as [y b2]. cbn in p.
  destruct p as [p q]. destruct p, q. cbn. refl.
Defined.

Definition sigma_eq_elim
  {A : U} {B : A -> U} {x y : {x : A & B x}} (p : x = y)
  : {p : pr1' x = pr1' y & transport B p (pr2' x) = pr2' y}.
Proof.
  destruct p. cbn. eapply (| refl _, _ |).
Unshelve.
  cbn. refl.
Defined.

Definition sigma_eq_elim_1
  {A : U} {B : A -> U} {x y : {x : A & B x}} (p : x = y)
  : pr1' x = pr1' y := pr1' (sigma_eq_elim p).

Lemma sigma_eq_comp :
  forall (A : U) (B : A -> U) (x y : {a : A & B a})
  (p : pr1' x = pr1' y) (q : transport B p (pr2' x) = pr2' y),
    sigma_eq_elim (sigma_eq_intro (| p, q |)) = (| p, q |).
Proof.
  destruct x, y. cbn. destruct p, q. compute. refl.
Defined.

Lemma sigma_eq_uniq :
  forall (A : U) (B : A -> U) (x y : {a : A & B a}) (p : x = y),
    sigma_eq_intro (sigma_eq_elim p) = p.
Proof.
  destruct p, x. cbn. refl.
Defined.

(* Theorem 2.7.2 *)
Theorem sigma_eq_elim_equiv :
  forall (A : U) (B : A -> U) (x y : {a : A & B a}),
    isequiv (@sigma_eq_elim A B x y).
Proof.
  intros. apply qinv_isequiv. unfold qinv.
  eapply (| sigma_eq_intro, _ |).
Unshelve.
  cbn. hsplit.
    unfold homotopy. destruct x, y. destruct x1. cbn in *.
      destruct x1, e. cbn. refl.
    unfold homotopy. destruct x, y. destruct x1. cbn in *. refl.
Defined.

Lemma sigma_uniq :
  forall (A : U) (B : A -> U) (z : {a : A & B a}),
    z = (| pr1' z, pr2' z |).
Proof.
  intros. apply sigma_eq_intro. cbn. eapply (| refl _, _ |).
Unshelve.
  cbn. refl.
Defined.

(* Theorem 2.7.4 *)
Theorem transport_sigma :
  forall (A : U) (B : A -> U) (P : forall x : {a : A & B a}, U)
  (x y : A) (p : x = y) (u : B x) (z : P (| x,  u |)),
    @transport A (fun x : A => {u : B x & P (| x, u |)}) x y p (| u, z |) =
    @dpair (B y) (fun u => P (| y, u |))
      (transport _ p u)
      (transport _
        (@sigma_eq_intro A B (| x, u |) (| y, transport _ p u |)
          (| p, refl (transport _ p u) |))
        z).
Proof.
  destruct p. cbn. refl.
Defined.

(* TODO: generalize theorem 2.6.5 *)

(* Characterization of paths between dependent pairs. *)
Lemma refl_sigma :
  forall (A : U) (B : A -> U) (x : {a : A & B a}),
    refl x = sigma_eq_intro (| refl (pr1' x), refl (pr2' x) |).
Proof.
  destruct x. cbn. refl.
Defined.

Lemma inv_sigma :
  forall (A : U) (B : A -> U) (x y : {a : A & B a}) (p : x = y), U.
Proof.
  intros.
Check inv (ap pr1' p).
Check inv (@apd {a : A & B a} (fun x => B (pr1' x)) pr2' _ _ (inv p)).
Check sigma_eq_intro (| inv (ap pr1' p), inv _ |).
Check transport _ (inv (ap pr1' p)) (pr2' y).
Check @sigma_eq_elim _ _ y x (inv p).
assert (pr2' x = transport _ (inv (ap pr1' p)) (pr2' y)).
  apply inv. rewrite <- ap_inv.
Abort.

Lemma cat_sigma :
  forall (A : U) (B : A -> U) (x y z : {a : A & B a})
  (p : x = y) (q : y = z), U.
Proof.

(*    cat p q =
  sigma_eq_intro (cat (ap pr1 p) (ap pr1 q), cat (ap pr2 p) (ap pr2 q)).
*)
Abort.

(** * 2.8 The unit type *)

Definition unit_eq_intro
  (x y : unit) (u : unit) : x = y :=
match x, y with
    | tt, tt => refl tt
end.

Definition unit_eq_elim
  {x y : unit} (p : x = y) : unit := tt.

Lemma unit_eq_comp :
  forall x y : unit,
    unit_eq_elim (unit_eq_intro x y tt) = tt.
Proof.
  destruct x, y. cbn. refl.
Defined.

Lemma unit_eq_uniq :
  forall (x y : unit) (p : x = y),
    unit_eq_intro x y (unit_eq_elim p) = p.
Proof.
  destruct p, x. cbn. refl.
Defined.

Theorem unit_eq_equiv :
  forall x y : unit,
    isequiv (unit_eq_intro x y).
Proof.
  intros. apply qinv_isequiv.
  unfold qinv. eapply (| @unit_eq_elim x y, _ |).
Unshelve.
  cbn. hsplit; compute.
    destruct x0, x. refl.
    destruct x0. refl.
Defined.

(** * Π-types and the function extensionality axiom *)

Definition happly {A : U} {B : A -> U}
  {f g : forall x : A, B x} (p : f = g) : forall x : A, f x = g x :=
  fun x : A =>
match p with
    | refl _ => refl _
end.

(*Axiom happly_isequiv :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x),
    isequiv (@happly A B f g).

Definition funext {A : U} {B : A -> U} {f g : forall x : A, B x}
  (h : forall x : A, f x = g x) : f = g.
Proof.
  pose (happly_isequiv A B f g). apply isequiv_qinv in i.
  destruct i. apply x, h.
Defined.

Lemma happly_funext :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x)
  (h : forall x : A, f x = g x) (x : A),
    happly (funext h) x = h x.
Proof.
  intros. 
  pose (happly_isequiv A B f g). apply isequiv_qinv in i.
  destruct i. unfold homotopy in p. destruct p. unfold funext. cbn.
Defined.*)

Axiom funext :
  forall {A : U} {B : A -> U} {f g : forall x : A, B x}
  (h : forall x : A, f x = g x), f = g.

Polymorphic Axiom happly_funext :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x)
  (h : forall x : A, f x = g x),
    happly (funext h) = h.

Axiom funext_happly :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x) (p : f = g),
    p = funext (fun x : A => happly p x).

Theorem funext_isequiv :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x),
    isequiv (@funext A B f g).
Proof.
  intros. apply qinv_isequiv. unfold qinv.
  eapply (| happly, _ |).
Unshelve.
  cbn. unfold homotopy, comp. hsplit; intros.
    rewrite <- funext_happly. refl.
    rewrite happly_funext. refl.
Defined.

Lemma refl_pi :
  forall (A : U) (B : A -> U) (f : forall x : A, B x),
    refl f = funext (fun x : A => refl (f x)).
Proof.
  intros. rewrite (@funext_happly _ _ f f (refl f)). cbn. refl.
Defined.

Lemma inv_pi :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x) (p : f = g),
    inv p = funext (fun x : A => happly (inv p) x).
Proof.
  destruct p. cbn. apply refl_pi.
Defined.

Lemma cat_pi :
  forall (A : U) (B : A -> U) (f g h : forall x : A, B x)
  (p : f = g) (q : g = h),
    cat p q = funext (fun x : A => cat (happly p x) (happly q x)).
Proof.
  destruct p, q. cbn. apply refl_pi.
Defined.

Lemma transport_fun :
  forall (Z : U) (A B : Z -> U) (x y : Z)
  (f : A x -> B x) (p : x = y),
    @transport Z (fun x : Z => A x -> B x) x y p f =
    fun x : A y => transport B p (f (transport A (inv p) x)).
Proof.
  destruct p. cbn. refl.
Defined.

Lemma transport_pi :
  forall
    (X : U) (A : X -> U) (B : forall x : X, A x -> U)
    (x1 x2 : X) (p : x1 = x2) (f : forall a : A  x1, B x1 a),
      @transport X (fun x : X => forall a : A x, B x a) x1 x2 p f =
      fun a : A x2 =>
        @transport {x : X & A x} (fun w => B (pr1' w) (pr2' w))
          (| x1, transport _ (inv p) a |) (| x2, a |)
          (inv (@sigma_eq_intro X A
            (| x2, a |) (| x1, transport _ (inv p) a |)
            (| inv p, refl (transport _ (inv p) a) |)))
          (f (transport _ (inv p) a)).
Proof.
  destruct p. cbn. refl.
Defined.

Ltac ehsplit := eapply (| _, _ |).

(* Lemma 2.9.6 *)
Lemma lemma_2_9_6 :
  forall
    (Z : U) (A B : Z -> U) (x y : Z) (p : x = y)
    (f : A x -> B x) (g : A y -> B y),
      (@transport Z (fun z : Z => A z -> B z) _ _ p f = g) ~
      (forall a : A x, transport _ p (f a) = g (transport _ p a)).
Proof.
  destruct p. cbn. intros.
  unfold equiv. eapply (| happly, _ |).
Unshelve.
  cbn. apply qinv_isequiv. unfold qinv. eapply (| funext, _ |).
Unshelve.
  cbn. unfold homotopy, comp. hsplit; intros.
    apply happly_funext.
    destruct x0. compute. rewrite funext_happly. cbn. refl.
Restart.
  destruct p. cbn. intros.
  apply equiv_sym. unfold equiv. eapply (| funext, _ |).
Unshelve.
  cbn. apply funext_isequiv.
Defined.

Check lemma_2_9_6.

Lemma lemma_2_9_7 :
  forall
    (Z : U) (A : Z -> U) (B : forall z : Z, A z -> U)
    (x y : Z) (p : x = y)
    (f : forall a : A x, B x a) (g : forall a : A y, B y a),
      (@transport Z (fun z : Z => forall a : A z, B z a) x y p f = g) ~
      (forall a : A x,
        @transport {x : Z & A x} (fun w => B (pr1' w) (pr2' w))
          (| x, a |) (| y, transport _ p a |)
          (@sigma_eq_intro Z A
            (| x, a |) (| y, transport _ p a |)
            (| p, refl (transport _ p a) |)) (f a)
        = g (transport _ p a)).
Proof.
  destruct p. cbn. intros.
  apply equiv_sym. unfold equiv. eapply (| funext, _ |).
Unshelve.
  cbn. apply funext_isequiv.
Defined.

(** ** 2.10 Universes and the univalence axiom *)

Lemma isequiv_id :
  forall A : U, isequiv (@id A).
Proof.
  intro. unfold isequiv. split.
    exists id. compute. refl.
    exists id. compute. refl.
Defined.

Lemma equiv_id :
  forall A : U, A ~ A.
Proof.
  intro. unfold equiv. exists id. apply isequiv_id.
Defined.

Definition idtoeqv {A B : U} (p : A = B) : equiv A B.
Proof.
  unfold equiv. exists (transport _ p).
  destruct p. cbn. apply isequiv_id.
Defined.

Axiom ua : forall {A B : U} (e : equiv A B), @eq U A B.

Definition apply_equiv {A B : U} (e : A ~ B) : A -> B := pr1' e.
Coercion apply_equiv : equiv >-> Funclass.

Axiom idtoeqv_ua :
  forall {A B : U} (e : A ~ B) (x : A),
    idtoeqv (ua e) x = e x.

Axiom idtoeqv_ua' :
  forall {A B : U} (e : A ~ B),
    idtoeqv (ua e) = e.

Axiom transport_ua :
  forall {A B : U} (e : A ~ B) (x : A),
    transport _ (ua e) x = e x.

Axiom ua_idtoeqv :
  forall {A B : U} (p : A = B),
    p = ua (idtoeqv p).

Axiom ua_transport :
  forall {A B : U} (p : A = B),
    p = ua (idtoeqv p).

Lemma ua_id :
  forall A : U, ua (equiv_id A) = refl A.
Proof.
  intro. rewrite ua_idtoeqv. apply ap. compute. refl.
Defined.

Lemma cat_ua :
  forall (A B C : U) (f : equiv A B) (g : equiv B C),
    cat (ua f) (ua g) = ua (equiv_trans _ _ _ f g).
Proof.
  intros.
  rewrite (ua_idtoeqv (ua f)), (ua_idtoeqv (ua g)).
  assert (forall (u : A),
    idtoeqv (cat (ua (idtoeqv (ua f))) (ua (idtoeqv (ua g)))) u =
    idtoeqv (ua (equiv_trans A B C f g)) u).
      intro. rewrite ?idtoeqv_ua. cbn.
      rewrite <- transport_cat, ?transport_ua, ?idtoeqv_ua.
      destruct f as [f [[f1 Hf1] [f2 Hf2]]], g as [g [[g1 Hg1] [g2 Hg2]]].
      compute. refl.
  assert (
    idtoeqv (cat (ua (idtoeqv (ua f))) (ua (idtoeqv (ua g)))) =
    idtoeqv (ua (equiv_trans A B C f g))).
      apply sigma_eq_intro. esplit. Unshelve.
        Focus 3. destruct (idtoeqv _), (idtoeqv _). cbn.
          apply funext. intro. cbn in X. apply X.
        destruct _. cbn. destruct (ua _). cbn in *. unfold transport.
          assert (p : id = x).
            apply funext. symmetry. apply X.
          destruct p.
          assert (funext (fun x => X x) =  refl id).
            rewrite refl_pi. apply ap. apply funext. intro. admit.
          rewrite X0. admit.
  apply (ap ua) in X0. rewrite <- !ua_idtoeqv in *.
    rewrite <- !ua_idtoeqv in X0. assumption.
Admitted.

(** ** 2.11 Identity types *)

Theorem ap_isequiv :
  forall (A B : U) (f : A -> B) (x y : A),
    isequiv f -> isequiv (@ap A B f x y).
Proof.
  intros. apply qinv_isequiv. apply isequiv_qinv in X.
  unfold qinv in *. destruct X as [g [H1 H2]].
  esplit.
Unshelve.
  Focus 2. intros. compute in *.
    apply (cat (inv (H2 x)) (cat (ap g X) (H2 y))).
  unfold homotopy, comp, id in *. hsplit; intros.
    Focus 2. destruct x0. rewrite ap_refl, cat_refl_l, cat_inv_l. refl.
    rewrite !ap_cat. rewrite !ap_inv. rewrite !ap_ap.
Restart.
  destruct 1 as [[g1 H1] [g2 H2]].
  unfold isequiv, homotopy, comp, id in *.
  split; esplit. Unshelve.
    Focus 3. intro p. exact (cat (inv (H2 x)) (cat (ap g2 p) (H2 y))).
      intros. cbn. rewrite !ap_cat, !ap_inv, !ap_ap. admit.
    Focus 2. intro p. exact (cat (inv (H2 x)) (cat (ap g2 p) (H2 y))).
Admitted.

(* Lemma 2.11.2 *)
Lemma transport_eq_l :
  forall (A : U) (a x y : A) (p : x = y) (q : a = x),
    @transport _ (fun x : A => a = x) _ _ p q = cat q p.
Proof.
  destruct p, q. cbn. refl.
Defined.

Lemma transport_eq_r :
  forall (A : U) (a x y : A) (p : x = y) (q : x = a),
    @transport _ (fun x : A => x = a) _ _ p q = cat (inv p) q.
Proof.
  destruct p, q. cbn. refl.
Defined.

Lemma transport_eq :
  forall (A : U) (x y : A) (p : x = y) (q : x = x),
    @transport _ (fun x : A => x = x) _ _ p q = cat (inv p) (cat q p).
Proof.
  destruct p. intros. rewrite cat_refl_r.
  change (inv (refl x)) with (refl x). rewrite cat_refl_l. cbn. refl.
Defined.

(* Theorem 2.11.3 *)
Theorem transport_eq_fun :
  forall (A B : U) (f g : A -> B) (x y : A) (p : x = y) (q : f x = g x),
    @transport _ (fun x => f x = g x) _ _ p q =
    cat (inv (ap f p)) (cat q (ap g p)).
Proof.
  destruct p. intros. rewrite cat_refl_r.
  change (inv (refl x)) with (refl x). rewrite cat_refl_l. cbn. refl.
Defined.

(* Theorem 2.11.4 *)
Theorem transport_eq_fun_dep :
  forall
    (A : U) (B : A -> U) (f g : forall x : A, B x)
    (x y : A) (p : x = y) (q : f x = g x),
      @transport _ (fun x => f x = g x) _ _ p q =
      cat (inv (apd f p)) (cat (ap (transport B p) q) (apd g p)).
Proof.
  destruct p. intros. rewrite cat_refl_r, cat_refl_l. cbn.
  rewrite ap_id. refl.
Defined.

(* Theorem 2.11.5 *)
Theorem transport_eq_isequiv :
  forall (A : U) (a x y : A) (p : x = y) (q : x = x) (r : y = y),
    equiv (@transport _ (fun x => x = x) _ _ p q = r) (cat q p = cat p r).
Proof.
  destruct p. intros. rewrite cat_refl_l, cat_refl_r. cbn. apply equiv_refl.
Defined.

(* TODO: 2.11, examples: products and functions *)

(** * 2.12 Coproducts *)

Definition code {A B : U} (a : A) (x : A + B) : U :=
match x with
    | inl a' => a = a'
    | inr b => empty
end.

Lemma code_char :
  forall (A B : U) (a : A) (x : A + B),
    equiv (inl a = x) (code a x).
Proof.
  intros. red. eapply (| _, _ |).
Unshelve.
  destruct x.
    destruct 1. unfold code. refl.
    intros. rewrite <- X. unfold code. refl.
  cbn. red. eapply (_, _).
Unshelve.
  all: eapply (| _, _ |).
Unshelve.
  unfold code. destruct x, 1. refl.
  cbn. compute. destruct x.
    destruct x. refl.
    destruct x.
  unfold code. destruct x, 1. refl.
  cbn. compute. destruct x0. refl.
Defined.

Definition encode
  {A B : U} (a : A) (x : A + B) (p : inl a = x) : code a x :=
    transport _ p (refl a).

Definition decode :
  forall (A B : U) (x : A + B) (a : A) (c : code a x),
    inl a = x.
Proof.
  destruct x; unfold code.
    intros. apply (ap inl c).
    destruct 1.
Defined.

(* TODO: encode-decode *)

Lemma transport_inl :
  forall (Z : U) (A B : Z -> U) (x y : Z) (p : x = y) (a : A x),
    @transport _ (fun x : Z => A x + B x) _ _ p (inl a) =
    inl (transport A p a).
Proof.
  destruct p. cbn. refl.
Defined.

Lemma transport_inr :
  forall (Z : U) (A B : Z -> U) (x y : Z) (p : x = y) (b : B x),
    @transport _ (fun x : Z => A x + B x) _ _ p (inr b) =
    inr (transport B p b).
Proof.
  destruct p. cbn. refl.
Defined.

(** Exercises *)

(** **** Ex. 1.6 *)

Definition prod' (A B : U) : U :=
  forall b : bool, if b then A else B.

Definition pair' {A B : U} (a : A) (b : B) : prod' A B :=
  fun x : bool =>
match x with
    | true => a
    | false => b
end.
Definition p1 {A B : U} (p : prod' A B) : A := p true.
Definition p2 {A B : U} (p : prod' A B) : B := p false.

Lemma prod'_uniq
  {A B : U} (p : prod' A B) : p = pair' (p1 p) (p2 p).
Proof.
  unfold pair', p1, p2. apply funext. destruct x; refl.
Defined.

Lemma prod'_ind
  {A B : U} {P : prod' A B -> U} (f : forall (a : A) (b : B), P (pair' a b))
  (p : prod' A B) : P p.
Proof.
  apply (transport _ (inv (prod'_uniq p))). apply f.
Defined.

Lemma prod'_computation
  {A B : U} {P : prod' A B -> U} (f : forall (a : A) (b : B), P (pair' a b))
  (a : A) (b : B) :
    prod'_ind f (pair' a b) = f a b.
Proof.
  unfold prod'_ind. cbn. assert (prod'_uniq (pair' a b) = refl _).
    compute. rewrite refl_pi. apply ap. apply funext. destruct x; refl.
  rewrite X. cbn. refl.
Defined.

(** **** Ex. 2.1 *)

Definition cat1 {A : U} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
  destruct p. assumption.
Defined.

Definition cat2 {A : U} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
  destruct q. assumption.
Defined.

Definition cat3 {A : U} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
  destruct p, q. refl.
Defined.

Lemma cat1_cat2 :
  forall {A : U} {x y z : A} (p : x = y) (q : y = z),
    cat1 p q = cat2 p q.
Proof.
  destruct p, q. cbn. refl.
Defined.

Lemma cat2_cat3 :
  forall {A : U} {x y z : A} (p : x = y) (q : y = z),
    cat2 p q = cat3 p q.
Proof.
  destruct p, q. cbn. refl.
Defined.

Lemma cat1_cat3 :
  forall {A : U} {x y z : A} (p : x = y) (q : y = z),
    cat1 p q = cat3 p q.
Proof.
  destruct p, q. cbn. refl.
Defined.

(** **** Ex. 2.2 *)

Lemma ex_2_2 :
  forall {A : U} {x y z : A} (p : x = y) (q : y = z),
    cat (cat1_cat2 p q) (cat2_cat3 p q) = cat1_cat3 p q.
Proof.
  destruct p, q. cbn. refl.
Defined.

(** **** Ex. 2.3 *)

Definition cat4
  {A : U} {x y z : A} (p : x = y) (q : y = z) : x = z :=
    transport _ q p.

Lemma cat1_cat4 :
  forall {A : U} {x y z : A} (p : x = y) (q : y = z),
    cat1 p q = cat4 p q.
Proof.
  destruct p, q. cbn. refl.
Defined.

(** **** Ex. 2.4 TODO *)

(* Zero dimensional: x = y, boundaries are points
   One  dimensional: p = q, boundaries are paths (zero dim)
   Two  dimensional: r = s, boundaries are one dimensional paths
   n+1  dimensional: t = u, boundaries are n dimensional paths
*)

Goal forall x y : N, x = y. Abort.
Goal forall (x y : N) (p q : x = y), p = q. Abort.
Goal forall (x y : N) (p q : x = y) (r s : p = q), r = s. Abort.

Fixpoint path (n : N) (A : U) : U :=
  forall x y : A,
match n with
    | 0 => x = y
    | S n' => path n' (x = y)
end.

Compute path 0 N.
Compute path 1 N.
Compute path (S 1) N.
Compute path (S (S 1)) N.

(** **** Ex. 2.5 *)

Definition def_2_3_6
  {A B : U} (f : A -> B) {x y : A} (p : x = y) :
    f x = f y -> transport _ p (f x) = f y.
Proof.
  Check transportconst p (f x). intro q.
  exact (cat (transportconst p (f x)) q).
Defined.

Definition def_2_3_7
  {A B : U} (f : A -> B) {x y : A} (p : x = y) :
    transport _ p (f x) = f y -> f x = f y.
Proof.
  destruct p. cbn. intro q. exact q.
Defined.

Lemma def_237_def_236 :
  forall {A B : U} (f : A -> B) {x y : A} (p : x = y) (q : f x = f y),
    def_2_3_7 f p (def_2_3_6 f p q) = q.
Proof.
  destruct p. cbn. destruct q. refl.
Defined.

Lemma def_236_def_237 :
  forall
    {A B : U} (f : A -> B) {x y : A}
    (p : x = y) (q : transport _ p (f x) = f y),
      def_2_3_6 f p (def_2_3_7 f p q) = q.
Proof.
  destruct p. cbn. destruct q. refl.
Defined.

Lemma isequiv_def_2_3_6 :
  forall {A B : U} (f : A -> B) {x y : A} (p : x = y),
    isequiv (def_2_3_6 f p).
Proof.
  intros. apply qinv_isequiv. unfold qinv.
  exists (def_2_3_7 f p). split; unfold comp, id; intro.
    apply def_236_def_237.
    apply def_237_def_236.
Defined.

Lemma isequiv_def_2_3_7 :
  forall {A B : U} (f : A -> B) {x y : A} (p : x = y),
    isequiv (def_2_3_7 f p).
Proof.
  intros. apply qinv_isequiv. unfold qinv.
  exists (def_2_3_6 f p). split; unfold comp, id; intro.
    apply def_237_def_236.
    apply def_236_def_237.
Defined.

(** **** Ex. 2.6 *)

Lemma ex_2_6 :
  forall {A : U} {x y z : A} (p : x = y),
    isequiv (@cat A x y z p).
Proof.
  intros. apply qinv_isequiv. unfold qinv.
  exists (cat (inv p)). split.
    intro q. destruct p, q. cbn. refl.
    intro q. destruct p, q. cbn. refl.
Defined.

(** **** Ex. 2.7 TODO *)
(** **** Ex. 2.8 TODO *)

(** **** Ex. 2.9 *)

Lemma fun_sum :
  forall A B C : U,
    (A + B -> C) = (A -> C) * (B -> C).
Proof.
  intros. apply ua. unfold equiv.
  exists (fun f => (fun a => f (inl a), fun b => f (inr b))).
  apply qinv_isequiv. unfold qinv.
  exists (fun '(f, g) x =>
          match x with
              | inl a => f a
              | inr b => g b
          end).
  split.
    compute. destruct x as [f g]. refl.
    compute. intro. apply funext. destruct x0; refl.
Defined.

Lemma pi_sum :
  forall (A B : U) (C : A + B -> U),
    (forall x : A + B, C x) =
    (forall a : A, C (inl a)) * (forall b : B, C (inr b)).
Proof.
  intros. apply ua. unfold equiv.
  exists (fun f => (fun a => f (inl a), fun b => f (inr b))).
  apply qinv_isequiv. unfold qinv.
  esplit. Unshelve.
    Focus 2. destruct 1 as [f g]. destruct x as [a | b]; [apply f | apply g].
    split; compute.
      destruct x; refl.
      intro. apply funext. destruct x0; refl.
Defined.

(** **** Ex. 2.10 *)

Lemma sigma_assoc :
  forall (A : U) (P : A -> U) (C : sigma P -> U),
    {x : A & {y : P x & C (| x, y |)}} =
    {p : {x : A & P x} & C p}.
Proof.
  intros. apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. destruct 1 as (x & y & c).
    exists (| x, y |). assumption.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. destruct 1 as [[x y] c].
    exists x. exists y. assumption.
  split.
    compute. destruct x as [[x y] c]. refl.
    compute. destruct x as [x [y c]]. refl.
Defined.

Lemma sigma_prod_assoc :
  forall (A : U) (B C : A -> U),
    {x : A & B x * C x} =
    {p : {x : A & B x} & C (pr1' p)}.
Proof.
  intros. apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. destruct 1 as [x [b c]]. exists (| x, b |). cbn. assumption.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. destruct 1 as [[x b] c]. exists x. split; assumption.
  split; compute.
    destruct x as [[x b] c]. refl.
    destruct x as [x [b c]]. refl.
Defined.

(** **** Ex. 2.11 TODO *)
(** **** Ex. 2.12 TODO *)

(** **** Ex. 2.13 *)

(** Let's try to solve an easier problem. *)

Definition code_unit (x y : unit) : U := unit.

Definition encode_unit {x y : unit} (p : x = y) : code_unit x y := tt.

Definition decode_unit {x y : unit} (c : code_unit x y) : x = y :=
match x, y with
    | tt, tt => refl tt
end.

Lemma decode_encode_unit :
  forall {x y : unit} (p : x = y),
    decode_unit (encode_unit p) = p.
Proof.
  destruct p, x. cbn. refl.
Defined.

Lemma encode_decode_unit :
  forall {x y : unit} (c : code_unit x y),
    encode_unit (decode_unit c) = c.
Proof.
  destruct c. compute. refl.
Defined.

Lemma unit_eq_char :
  forall x y : unit,
    (x = y) = code_unit x y.
Proof.
  intros. apply ua. unfold equiv.
  exists encode_unit.
  apply qinv_isequiv. unfold qinv.
  exists decode_unit.
  split; compute.
    destruct x0. refl.
    destruct x0, x. refl.
Defined.

Lemma ex_2_13_aux :
  forall p : unit = unit, p = refl unit.
Proof.
  intro. rewrite (ua_idtoeqv p).
  assert (idtoeqv p = idtoeqv (refl unit)).
    apply sigma_eq_intro. esplit. Unshelve.
      Focus 3. destruct (idtoeqv p). compute. apply funext.
        destruct x0. destruct (x tt). refl.
      apply prod_eq_intro. split; apply sigma_eq_intro; cbn; esplit. Unshelve.
        Focus 4. destruct (transport isequiv _). cbn.
          destruct s. cbn. apply funext. destruct x0, (x tt). refl.
        Focus 4. destruct (transport isequiv _). cbn. destruct s0. cbn.
          apply funext. destruct x0, (x tt). refl.
        apply funext. destruct x.
          rewrite <- (decode_encode_unit (_ tt)).
          destruct (encode_unit _). cbn. refl.
        apply funext. destruct x.
          rewrite <- (decode_encode_unit (_ tt)).
          destruct (encode_unit _). cbn. refl.
    rewrite X. rewrite ua_id. refl.
Defined.

Lemma ex_2_13_aux' :
  (unit = unit) = unit.
Proof.
  apply ua. unfold equiv.
  exists (fun _ => tt).
  apply qinv_isequiv. unfold qinv.
  exists (fun _ => refl unit).
  split; compute.
    destruct x. refl.
    symmetry. apply ex_2_13_aux.
Defined.

Definition code_bool (b1 b2 : bool) : U :=
match b1, b2 with
    | false, false => unit
    | false, true => empty
    | true, false => empty
    | true, true => unit
end.

Definition encode_bool_aux (b : bool) : code_bool b b :=
match b with
    | true => tt
    | false => tt
end.

Definition encode_bool {b1 b2 : bool} (p : b1 = b2) : code_bool b1 b2 :=
  transport _ p (encode_bool_aux b1).

Definition decode_bool {b1 b2 : bool} (c : code_bool b1 b2) : b1 = b2.
Proof.
  destruct b1, b2; destruct c; refl.
Defined.

Lemma decode_encode_bool :
  forall {b1 b2 : bool} (p : b1 = b2),
    decode_bool (encode_bool p) = p.
Proof.
  destruct p, b1; cbn; refl.
Defined.

Lemma encode_decode_bool :
  forall {b1 b2 : bool} (c : code_bool b1 b2),
    encode_bool (decode_bool c) = c.
Proof.
  destruct b1, b2, c; refl.
Defined.

Lemma bool_eq_char :
  forall x y : bool,
    (x = y) = code_bool x y.
Proof.
  intros. apply ua. unfold equiv.
  exists encode_bool.
  apply qinv_isequiv. unfold qinv.
  exists decode_bool.
  split; unfold comp, id; intro.
    apply encode_decode_bool.
    apply decode_encode_bool.
Defined.

Definition negb (b : bool : U) : bool : U :=
match b with
    | false => true
    | true => false
end.

Lemma isequiv_negb : isequiv negb.
Proof.
  apply qinv_isequiv. unfold qinv. exists negb. split.
    compute. destruct x; refl.
    compute. destruct x; refl.
Defined.

Lemma negb_equiv : bool ~ bool.
Proof.
  unfold equiv. exists negb. apply isequiv_negb.
Defined.

Lemma neq_false_true : ~ false = true.
Proof.
  intro p.
  exact
  (@transport _ (fun b : bool => if b then empty else unit) _ _ p tt).
Defined.

Lemma isequiv_bool_char :
  forall f : bool -> bool,
    isequiv f -> (f = id) + (f = negb).
Proof.
  intros f e. assert ((f true = true) + (f true = false)).
    destruct (f true); [left | right]; refl.
  destruct e as [[g Hg] [h Hh]]. unfold homotopy, comp, id in *.
  destruct X; [left | right].
    apply funext. destruct x.
      assumption.
      assert ((f false = false) + (f false = true)).
        destruct (f false); [right | left]; refl.
        destruct X.
          assumption.
          cut empty.
            destruct 1.
            apply neq_false_true.
              apply (ap h) in e. rewrite Hh in e.
              apply (ap h) in e0. rewrite Hh in e0.
              rewrite e, e0. refl.
    apply funext. destruct x; cbn.
      assumption.
      assert ((f false = true) + (f false = false)).
        destruct (f false); [left | right]; refl.
        destruct X.
          assumption.
          cut empty.
            destruct 1.
            apply neq_false_true.
              apply (ap h) in e. rewrite Hh in e.
              apply (ap h) in e0. rewrite Hh in e0.
              rewrite e0, <- e. refl.
Defined.

Lemma isProp_isequiv_bool :
  forall (f : bool -> bool) (e1 e2 : isequiv f),
    e1 = e2.
Proof.
  intros. destruct e1 as [[g1 Hg1] [h1 Hh1]], e2 as [[g2 Hg2] [h2 Hh2]].
  unfold homotopy, comp, id in *.
  apply prod_eq_intro. split; apply sigma_eq_intro; cbn; esplit.
Unshelve.
  Focus 3. apply funext. intro.
    rewrite <- (Hh1 (g1 x)), <- (Hh1 (g2 x)). rewrite Hg1, Hg2. refl.
  compute. apply funext. intro b. destruct (funext _).
    rewrite <- (decode_encode_bool (Hg1 b)),
            <- (decode_encode_bool (Hg2 b)).
    generalize (Hg1 b), (Hg2 b). generalize (f (g1 b)).
      unfold encode_bool. destruct b0; cbn; intro.
        destruct e0, (transport _), (transport _). refl.
        destruct e0, (transport _), (transport _). refl.
  Focus 2. apply funext. intro.
    rewrite <- (Hg1 x), Hh1, Hh2. refl.
  compute. apply funext. intro b. destruct (funext _).
    rewrite <- (decode_encode_bool (Hh1 b)),
            <- (decode_encode_bool (Hh2 b)).
    generalize (Hh1 b), (Hh2 b). generalize (h1 (f b)).
      unfold encode_bool. destruct b0; cbn; intro.
        destruct e0, (transport _), (transport _). refl.
        destruct e0, (transport _), (transport _). refl.
Defined.

Lemma equiv_bool_bool_char :
  forall e : bool ~ bool,
    (e = equiv_id bool) + (e = negb_equiv).
Proof.
  destruct e as [f e].
    destruct (isequiv_bool_char f e).
      left. apply sigma_eq_intro. exists e0. apply isProp_isequiv_bool.
      right. apply sigma_eq_intro. exists e0. apply isProp_isequiv_bool.
Defined.

Lemma path_bool_bool_char :
  forall p : bool = bool,
    (p = refl bool) + (p = ua negb_equiv).
Proof.
  intro. destruct (equiv_bool_bool_char (idtoeqv p)); apply (ap ua) in e.
    left. rewrite <- ua_idtoeqv in e.
      rewrite e. Search ua. rewrite ua_id. refl.
    right. rewrite <- ua_idtoeqv in e. rewrite e. refl.
Defined.

Lemma ex_2_13 : (bool = bool) = bool.
Proof.
  apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. intro p. exact (transport id p true).
  apply qinv_isequiv. unfold qinv.
    exists (fun b : bool => if b then refl bool else ua negb_equiv). split.
      intro. destruct x.
        cbn. refl.
        unfold comp, id. rewrite transport_ua. cbn. refl.
      intro p. destruct (path_bool_bool_char p).
        rewrite e; compute. refl.
        unfold comp, id. rewrite e. rewrite transport_ua. cbn. refl.
Defined.

(** **** Ex. 2.14 *)

(** If we assume p : x = y gives x ≡ y, then refl x : x = y and by
    path induction we have p = refl x. *)

(** **** Ex. 2.15 *)

Lemma ex_2_15 :
  forall (A : U) (B : A -> U) (x y : A) (p : x = y),
    transport B p = idtoeqv (ap B p).
Proof.
  intros. destruct p. cbn. refl.
Defined.

(** **** Ex. 2.16 *)

(** **** Ex. 2.17 *)

Lemma ex_2_17_1_1 :
  forall {A A' B B' : U} (ea : A ~ A') (eb : B ~ B'),
    A * B ~ A' * B'.
Proof.
  intros. apply ua in ea. apply ua in eb. destruct ea, eb.
  apply idtoeqv. refl.
Defined.

Lemma ex_2_17_1_2 :
  forall {A A' B B' : U} (ea : A ~ A') (eb : B ~ B'),
    A * B ~ A' * B'.
Proof.
  destruct 1 as [f ef], 1 as [g eg].
  apply isequiv_qinv in ef. destruct ef as [f' [Hf1 Hf2]].
  apply isequiv_qinv in eg. destruct eg as [g' [Hg1 Hg2]].
  unfold equiv.
(*  exists (fun '(a, b) => (f a, g b)).
  apply qinv_isequiv. unfold qinv.
  exists (fun '(a', b') => (f' a', g' b')).
*)
  exists (fun x => (f (pr1 x), g (pr2 x))).
  apply qinv_isequiv. unfold qinv.
  exists (fun x => (f' (pr1 x), g' (pr2 x))).
  split; unfold homotopy, comp, id in *; destruct x; cbn.
    rewrite Hf1, Hg1. refl.
    rewrite Hf2, Hg2. refl.
Defined.

Lemma ex_2_17_1_2' :
  forall {A A' B B' : U} (ea : A ~ A') (eb : B ~ B'),
    A * B ~ A' * B'.
Proof.
  destruct 1 as [f [[f1 Hf1] [f2 Hf2]]],
           1 as [g [[g1 Hg1] [g2 Hg2]]].
  unfold equiv.
(*  exists (fun '(a, b) => (f a, g b)).
  apply qinv_isequiv. unfold qinv.
  exists (fun '(a', b') => (f' a', g' b')).
*)
  exists (fun x => (f (pr1 x), g (pr2 x))).
  unfold isequiv. split.
    exists (fun x => (f1 (pr1 x), g1 (pr2 x))).
      compute in *. destruct x. rewrite Hf1, Hg1. refl.
    exists (fun x => (f2 (pr1 x), g2 (pr2 x))).
      compute in *. destruct x. rewrite Hf2, Hg2. refl.
Defined.

Lemma aux : 
  forall A B : U,
    (forall x : A * B, (pr1 x, pr2 x) = x) =
    (forall x : A * B, x = x).
Proof.
  intros. apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. intros. destruct x. apply (X (a, b)).
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. intros. destruct x. cbn. apply X.
  split; compute; intro; apply funext; destruct x0; refl.
Defined.

Lemma ex_2_17_2 :
  forall (A A' B B' : U) (ea : A ~ A') (eb : B ~ B'),
    ex_2_17_1_1 ea eb = ex_2_17_1_2 ea eb.
Proof.
  intros.
  rewrite <- (idtoeqv_ua' ea), <- (idtoeqv_ua' eb).
  unfold ex_2_17_1_1. destruct (ua ea), (ua eb).
  rewrite 2!ua_id. cbn.
  unfold idtoeqv, isequiv_id, transport, id.
  Check fun x : A * B =>
 match x as p return ((pr1 p, pr2 p) = p) with
 | (a, b) => refl (a, b)
 end.

  assert (
          transport id (aux A B) (fun x : A * B =>
          match x as p return ((pr1 p, pr2 p) = p) with
              | (a, b) => refl (a, b)
          end)
          =
          fun x => refl x).
    apply funext. destruct x.
Restart.
  intros. unfold ex_2_17_1_1, ex_2_17_1_2.
  destruct ea, eb, (ua (| x, i |)), (ua (| x0, i0 |)).
  destruct (isequiv_qinv _), (isequiv_qinv _), p, p0.
Abort.

Lemma ex_2_17_2' :
  forall (A A' B B' : U) (ea : A ~ A') (eb : B ~ B'),
    ex_2_17_1_1 ea eb = ex_2_17_1_2' ea eb.
Proof.
  intros. unfold ex_2_17_1_1, ex_2_17_1_2.
  destruct ea, eb, (ua (| x, i |)), (ua (| x0, i0 |)).
  destruct i as [[] []], i0 as [[] []].
  compute.
  apply sigma_eq_intro. esplit. Unshelve.
    Focus 2. cbn. apply funext. destruct x5. admit.
    compute. Search funext.
Abort.

Lemma sum_pres_equiv :
  forall A A' B B' : U,
    A ~ A' -> B ~ B' -> (A + B) ~ (A' + B').
Proof.
  intros * p q. apply ua in p. apply ua in q. destruct p, q.
  apply idtoeqv. refl.
Defined.

Lemma ua_equiv_sym :
  forall (A B : U) (e : A ~ B),
    ua (equiv_sym _ _ e) = inv (ua e).
Proof.
  intros. unfold inv. destruct (ua e).
  rewrite ua_idtoeqv.
  apply ap. 
  destruct e as [f [[f1 H1] [f2 H2]]].
  compute. apply sigma_eq_intro. esplit.
Abort.

Lemma sigma_pres_equiv :
  forall (A A' : U) (B : A -> U) (B' : A' -> U)
    (ea : A ~ A') (eb : forall x : A, B x ~ B' (transport _ (ua ea) x)),
      sigma B ~ sigma B'.
Proof.
  intros. unfold equiv. esplit.
Unshelve.
  Focus 2. destruct 1 as [x y]. exists (transport _ (ua ea) x).
    exact (transport id (ua (eb x)) y).
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. destruct 1 as [x y].
    exists (transport _ (ua (equiv_sym _ _ ea)) x).
    rewrite transport_ua. assert (A = A').
      apply ua, ea.
    destruct X.
    destruct ea as [f [[f1 H1] [f2 H2]]].
    cbn. unfold homotopy, comp, id in *. rewrite H1.
Abort.

(** Chapter 3 *)

Definition isSet (A : U) : U :=
  forall (x y : A) (p q : x = y), p = q.

Lemma isSet_empty : isSet empty.
Proof.
  unfold isSet. destruct x.
Defined.

Lemma isSet_unit : isSet unit.
Proof.
  unfold isSet. intros.
  rewrite <- (unit_eq_uniq _ _ p), <- (unit_eq_uniq _ _ q).
  compute. destruct x, y. refl.
Defined.

Lemma isSet_bool : isSet bool.
Proof.
  unfold isSet. intros.
  rewrite <- (decode_encode_bool p), <- (decode_encode_bool q).
  destruct p, x; cbn.
    destruct (encode_bool q). refl.
    destruct (encode_bool q). refl.
Defined.

(* encode-decode for N *)
Fixpoint code_N (n m : N) : U :=
match n, m with
    | 0, 0 => unit
    | 0, _ => empty
    | _, 0 => empty
    | S n', S m' => code_N n' m'
end.

Fixpoint encode_N_aux (n : N) : code_N n n :=
match n with
    | 0 => tt
    | S n' => encode_N_aux n'
end.

Definition encode_N {n m : N} (p : n = m) : code_N n m :=
  transport _ p (encode_N_aux n).

Fixpoint decode_N {n m : N} (c : code_N n m) {struct n} : n = m.
Proof.
  destruct n as [| n'], m as [| m']; cbn in *.
    refl.
    destruct c.
    destruct c.
    exact (ap S (decode_N _ _ c)).
Defined.

Lemma decode_encode_N :
  forall (n m : N) (p : n = m),
    decode_N (encode_N p) = p.
Proof.
  unfold encode_N. destruct p. cbn. induction n as [| n']; cbn.
    refl.
    unfold id in IHn'. rewrite IHn'. cbn. refl.
Defined.

Lemma code_N_isProp :
  forall (n m : N) (c1 c2 : code_N n m),
    c1 = c2.
Proof.
  induction n as [| n'], m as [| m']; cbn.
    1-3: destruct c1, c2. refl.
    intros. apply IHn'.
Defined.

Lemma isSet_N : isSet N.
Proof.
  unfold isSet. intros.
  rewrite <- (decode_encode_N _ _ p), <- (decode_encode_N _ _ q).
  rewrite (code_N_isProp x y (encode_N p) (encode_N q)). refl.
Defined.

Lemma isSet_prod :
  forall A B : U,
    isSet A -> isSet B -> isSet (A * B).
Proof.
  unfold isSet. intros. Search prod.
  rewrite (prod_eq_uniq _ _ _ _ p), (prod_eq_uniq _ _ _ _ q).
  rewrite (X _ _ (ap pr1 p) (ap pr1 q)),
          (X0 _ _ (ap pr2 p) (ap pr2 q)).
  refl.
Defined.

Lemma isSet_pi :
  forall (A : U) (B : A -> U),
    (forall x : A, isSet (B x)) -> isSet (forall x : A, B x).
Proof.
  unfold isSet. intros.
  rewrite (funext_happly _ _ _ _ p), (funext_happly _ _ _ _ q).
  apply ap. apply funext. intro.
  rewrite (X x0 (x x0) (y x0) (happly p x0) (happly q x0)). refl.
Defined.

Definition type1 (A : U) : U :=
  forall (x y : A) (p q : x = y) (r s : p = q), r = s.

Lemma isSet_type1 :
  forall A : U, isSet A -> type1 A.
Proof.
  unfold isSet, type1. intros.
  pose (g q := X x y p q).
  pose (H := apd g r).
  rewrite transport_eq_l in H.
  pose (H' := apd g s).
  rewrite transport_eq_l in H'.
  apply (ap (fun r => cat (inv (g p)) r)) in H.
  apply (ap (fun r => cat (inv (g p)) r)) in H'.
  rewrite cat_assoc in *. rewrite cat_inv_l in *.
  rewrite cat_refl_l in *. rewrite H, H'.
  refl.
Defined.

Definition const {A : U} (x y : A) : A := x.

Lemma isSet_U_not :
  ~ isSet U.
Proof.
  unfold isSet. intro.
  assert (false = true).
    assert (@transport _ id _ _ (ua negb_equiv) false = true).
      apply (transport_ua negb_equiv false).
      rewrite (X _ _ _ (refl bool)) in X0. cbn in X0. assumption.
    apply neq_false_true. assumption.
Defined.

Theorem not_DNE :
  ~ forall A : U, ~ ~ A -> A.
Proof.
  intro f.
  pose (p := ua negb_equiv).
  pose (u := fun f : ~ bool => f true).
  assert (transport (fun X : U => ~ ~ X -> X) p (f bool) u = f bool u).
    rewrite (apd f p). refl.
    rewrite transport_fun in X.
      assert (transport (fun X : U => ~ ~ X) (inv p) u = u).
        apply funext. intro. destruct (u x).
        rewrite X0 in X. unfold p in X. rewrite transport_ua in X.
          destruct (f bool u); cbn in X.
            apply neq_false_true. assumption.
            apply neq_false_true. apply inv. assumption.
Defined.

Lemma triple_neg :
  forall A : U, ~ ~ ~ A -> ~ A.
Proof.
  repeat intro. apply X. intro. apply X1. assumption.
Defined.

(*
Lemma DNE_to_LEM :
  (forall A : U, ~ ~ A -> A) -> forall A : U, A + ~ A.
Proof.
  intros. apply X. intro. assert (~ A * ~ A).
    intro. destruct X1. apply n. assumption.
*)

Definition bad_LEM : U := forall A : U, A + ~ A.
Definition bad_DNE : U := forall A : U, ~ ~ A -> A.

Lemma bad_LEM_to_bad_DNE : bad_LEM -> bad_DNE.
Proof.
  unfold bad_LEM, bad_DNE. intros.
  destruct (X A).
    assumption.
    assert empty.
      apply X0. assumption.
      destruct X1.
Defined.

Theorem not_bad_LEM : ~ bad_LEM.
Proof.
  intro. apply not_DNE. apply bad_LEM_to_bad_DNE. assumption.
Defined.

Lemma not_Prop_making_functor :
  forall F : U -> U,
    (forall (A : U) (x y : F A), x = y) -> F bool ->
      ~ forall A : U, F A -> A.
Proof.
  intros F H u f.
  pose (p := ua negb_equiv).
  assert (transport (fun X : U => F X -> X) p (f bool) u = f bool u).
    rewrite (apd f p). refl.
    rewrite transport_fun, (H _ _ u) in X. unfold p in X.
      rewrite transport_ua in X. destruct (f bool u); cbn in X.
        apply neq_false_true. assumption.
        apply neq_false_true. apply inv. assumption.
Defined.

(** 3.3 Mere propositions *)

Definition isProp (P : U) : U :=
  forall x y : P, x = y.

Lemma isProp_empty : isProp empty.
Proof.
  unfold isProp. destruct x.
Defined.

Lemma isProp_unit : isProp unit.
Proof.
  unfold isProp. destruct x, y. refl.
Defined.

Lemma inhabited_isProp_unit :
  forall P : U, isProp P -> P -> P ~ unit.
Proof.
  unfold isProp, equiv. intros P H x.
  exists (fun _ => tt). apply qinv_isequiv. unfold qinv.
  exists (fun _ => x). split.
    compute. destruct x0. refl.
    compute. apply H.
Defined.

Lemma inhabited_isProp_unit' :
  forall P : U, isProp P -> P -> P = unit.
Proof.
  intros. apply ua. apply inhabited_isProp_unit; assumption.
Defined.

Lemma isProp_both_impls_equiv :
  forall P Q : U,
    isProp P -> isProp Q -> (P -> Q) -> (Q -> P) -> P ~ Q.
Proof.
  unfold isProp, equiv. intros P Q HP HQ f g.
  exists f. apply qinv_isequiv. unfold qinv.
  exists g. split; compute; intro.
    apply HQ.
    apply HP.
Defined.

Lemma isProp_isSet :
  forall P : U, isProp P -> isSet P.
Proof.
  unfold isProp, isSet. intros P H x y p q.
  pose (apd (H x) p).
  pose (apd (H x) q).
  assert (transport (eq x) p (H x x) = transport (eq x) q (H x x)).
    rewrite e, e0. refl.
    rewrite ?transport_eq_l in X.
    assert (cat (cat (inv (H x x)) (H x x)) p =
            cat (cat (inv (H x x)) (H x x)) q).
      rewrite <- !cat_assoc. rewrite X. refl.
      rewrite !cat_inv_l, !cat_refl_l in X0. assumption.
Defined.

Lemma isProp_isProp :
  forall P : U, isProp (isProp P).
Proof.
  intros P f g. do 2 (apply funext; intro).
  assert (isSet P).
    apply isProp_isSet. assumption.
    unfold isSet in X. apply X.
Defined.

Lemma isProp_isSet' :
  forall A : U, isProp (isSet A).
Proof.
  unfold isProp, isSet. intros.
  do 4 (apply funext; intro).
  assert (type1 A).
    apply isSet_type1. assumption.
    unfold type1 in X. apply X.
Defined.

Definition LEM : U :=
  forall P : U, isProp P -> P + ~ P.

Definition DNE : U :=
  forall P : U, isProp P -> ~ ~ P -> P.

Definition decidable (A : U) : U := A + ~ A.

Definition decidable_family {A : U} (B : A -> U) : U :=
  forall x : A, decidable (B x).

Definition decidable_equality (A : U) : U :=
  forall x y : A, (x = y) + ~ (x = y).

(** ** 3.5 Subsets and propositional resizing *)

Lemma lemma_3_5_1 :
  forall (A : U) (P : A -> U),
    (forall x : A, isProp (P x)) ->
      forall u v : sigma P, pr1' u = pr1' v -> u = v.
Proof.
  intros. apply sigma_eq_intro. exists X0.
  unfold isProp in X. apply X.
Defined.

Definition set : U := {A : U & isSet A}.
Coercion set_to_Sortclass (s : set) : U := pr1' s.

Definition prop : U := {P : U & isProp P}.
Coercion prop_to_Sortclass (p : prop) : U := pr1' p.

(** ** 3.6 The logic of mere propositions *)

Lemma isProp_prod :
  forall A B : U, isProp A -> isProp B -> isProp (A * B).
Proof.
  unfold isProp. intros A B HA HB x y. apply prod_eq_intro. split.
    apply HA.
    apply HB.
Defined.

Lemma isProp_pi :
  forall (A : U) (B : A -> U),
    (forall x : A, isProp (B x)) -> isProp (forall x : A, B x).
Proof.
  unfold isProp. intros A B H f g. apply funext. intro. apply H.
Defined.

Lemma isProp_fun :
  forall A B : U, isProp B -> isProp (A -> B).
Proof.
  intros. apply isProp_pi. intro. assumption.
Defined.

Lemma isProp_sum :
  ~ forall A B : U, isProp A -> isProp B -> isProp (A + B).
Proof.
  unfold isProp. intro H. Search isProp.
  specialize (H unit unit isProp_unit isProp_unit (inl tt) (inr tt)).
  apply code_char in H. cbn in H. assumption.
Defined.

(** ** 3.7 Propositional truncation *)

Axiom trunc : U -> U.
Axiom trunc' : forall {A : U}, A -> trunc A.
Axiom path : forall {A : U} (x y : trunc A), x = y.

Axiom trunc_rec :
  forall {A B : U},
    isProp B -> (A -> B) -> trunc A -> B.

(*
Axiom trunc_ind :
  forall {A : U} {B : A -> U},
    (forall x : A, isProp (B x)) -> (forall x : A, B x) -> forall x : trunc A, B x.
*)
Axiom trunc_comp :
  forall (A B : U) (H : isProp B) (f : A -> B) (x : A),
    trunc_rec H f (trunc' x) = f x.

Definition or (P Q : U) : U := trunc (P + Q).
Definition ex {A : U} (P : A -> U) : U := trunc (sigma P).

Lemma isProp_trunc :
  forall A : U, isProp (trunc A).
Proof.
  unfold isProp. intros. apply path.
Defined.

(** ** 3.8 The axiom of choice *)

Definition AC : U :=
  forall (X : U) (A : X -> U) (P : forall x : X, A x -> U),
    isSet X -> (forall x : X, isSet (A x)) ->
    (forall (x : X) (a : A x), isProp (P x a)) ->
      (forall x : X, trunc {a : A x & P x a}) ->
      trunc {f : forall x : X, A x & forall x : X, P x (f x)}.

Definition AC' : U :=
  forall (X : U) (A : X -> U) (P : forall x : X, A x -> U),
    isSet X -> (forall x : X, isSet (A x)) ->
    (forall (x : X) (a : A x), isProp (P x a)) ->
      (forall x : X, trunc {a : A x & P x a}) ->
      trunc {f : forall x : X, A x & forall x : X, P x (f x)}.

Definition PNE : U :=
  forall (X : U) (Y : X -> U),
    isSet X -> (forall x : X, isSet (Y x)) ->
      (forall x : X, trunc (Y x)) -> trunc (forall x : X, Y x).

(** **** Ex. 3.3 *)

Lemma isSet_sigma :
  forall (A : U) (B : A -> U),
    isSet A -> (forall x : A, isSet (B x)) ->
      isSet (sigma B).
Proof.
  unfold isSet. intros A B SA SB x y p q.
  assert (P : isProp {p : pr1' x = pr1' y & transport B p (pr2' x) = pr2' y}).
    unfold isProp. intros. apply sigma_eq_intro.
      exists (SA _ _ (pr1' x0) (pr1' y0)). apply SB.
  rewrite <- (sigma_eq_uniq _ _ _ _ p), <- (sigma_eq_uniq _ _ _ _ q).
  unfold isProp in P.
  rewrite (P _ (sigma_eq_elim q)). refl.
Defined.

Lemma AC_PNE : AC = PNE.
Proof.
  apply ua. unfold equiv. esplit. apply qinv_isequiv. esplit.
Unshelve.
  2:
  {
    unfold AC, PNE. intros AC X Y HX HY f.
    specialize (AC X Y (fun _ _ => unit) HX HY (fun _ _ => isProp_unit)).
    assert (forall x : X, trunc {a : Y x & (fun _ _ => unit) x a}).
      intro. specialize (f x). revert f. apply trunc_rec.
        apply isProp_trunc.
        intro. exact (trunc' (| X0, tt |)).
      specialize (AC X0). revert AC. apply trunc_rec.
        apply isProp_trunc.
        intro. destruct X1. apply trunc'. assumption.
  }
  2:
  {
    unfold PNE, AC. intros PNS X A P HX HA HP f.
    specialize (PNS X (fun x : X => sigma (P x)) HX).
    assert (forall x : X, isSet ((fun x0 : X => {x : A x0 & P x0 x}) x)).
      intro. apply isSet_sigma.
        apply HA.
        intro. apply isProp_isSet. apply HP.
    specialize (PNS X0 f). revert PNS. apply trunc_rec.
      apply isProp_trunc.
      intro. apply trunc'. exists (fun x : X => pr1' (X1 x)). intro.
        destruct (X1 x). cbn. assumption.
  }
  split.
    unfold homotopy, comp, id. intros. repeat (apply funext; intro). apply path.
    unfold homotopy, comp, id. intros. repeat (apply funext; intro). apply path.
Defined.

Definition PNE' : U :=
  forall (X : U) (Y : X -> U),
    isSet X -> (forall x : X, isSet (Y x)) ->
      (forall x : X, trunc (Y x)) ~ trunc (forall x : X, Y x).

Lemma AC_PNE' : AC -> PNE'.
Proof.
  intro f. unfold PNE'. intros X Y SX SY. unfold equiv.
  rewrite AC_PNE in f. unfold PNE in f. exists (f X Y SX SY).
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. intros. revert X0. apply trunc_rec.
    apply isProp_trunc.
    intro. apply trunc'. apply X0.
  split.
    compute. intro. apply isProp_trunc.
    compute. intro. apply funext. intro. apply isProp_trunc.
Defined.

Definition bad_PNE
  (X : U) (Y : X -> U) : U :=
    (forall x : X, isSet (Y x)) ->
      (forall x : X, trunc (Y x)) -> trunc (forall x : X, Y x).

Lemma lemma_3_8_5 :
  {X : U & {Y : X -> U & (forall x : X, isSet (Y x)) * ~ bad_PNE X Y}}.
Proof.
  exists (sigma (fun X : U => trunc (bool = X))).
  pose (x := (| bool, trunc' (refl bool) |) : {X : U & trunc (bool = X)}).
  exists (fun y => x = y).
  assert (forall x0 : {X : U & trunc (bool = X)}, isSet (x = x0)).
    destruct x0 as (A & p). assert (isSet A).
      revert p. apply trunc_rec.
        apply isProp_isSet'.
        intro. destruct X. apply isSet_bool.
      admit.
    split.
      exact X.
      unfold bad_PNE. intro. specialize (X0 X).
        assert (forall x0 : {X : U & trunc (bool = X)}, trunc (x = x0)).
          destruct x0. revert t.
Abort.

(** ** 3.9 The principle of unique choice *)

(** ** 3.11 Contractibility *)

Definition isContr (A : U) : U :=
  sigma (fun x : A => forall y : A, x = y).

Lemma equiv_isContr_unit :
  forall A : U,
    isContr A -> A ~ unit.
Proof.
  unfold isContr. destruct 1. unfold equiv.
  exists (fun _ => tt). apply qinv_isequiv. unfold qinv.
  exists (fun _ => x). split.
    compute. destruct x0. refl.
    compute. exact e.
Defined.

Lemma isContr_isProp :
  forall A : U,
    isContr A -> isProp A.
Proof.
  unfold isContr, isProp. destruct 1. intros.
  rewrite <- (e x0), <- (e y). refl.
Defined.

Lemma isProp_isContr :
  forall A : U, isProp (isContr A).
Proof.
  unfold isProp. intros A c1 c2.
  assert (S : isSet A).
    apply isProp_isSet. apply isContr_isProp. assumption.
  destruct c1 as [x p], c2 as [y q].
  apply sigma_eq_intro. exists (p y). cbn.
  unfold isSet in S. apply funext. intro. apply S.
Defined.

Lemma isContr_isContr :
  forall A : U, isContr A -> isContr (isContr A).
Proof.
  intros A c. exists c. apply isProp_isContr.
Defined.

Lemma isContr_pi :
  forall (A : U) (P : A -> U),
    (forall x : A, isContr (P x)) ->
      isContr (forall x : A, P x).
Proof.
  unfold isContr. intros.
  exists (fun x => pr1' (X x)). intro. apply funext. intro.
  destruct (X x). cbn. apply e.
Defined.

Lemma isContr_fun :
  forall A B : U,
    isContr B -> isContr (A -> B).
Proof.
  unfold isContr. intros A B [x p]. exists (fun _ => x).
  intro. apply funext. intro. apply p.
Defined.

(* TODO: lemma 3.11.7 *)

Lemma lemma_3_11_8 :
  forall (A : U) (c : A),
    isContr (sigma (fun x : A => c = x)).
Proof.
  unfold isContr. intros.
  exists (| c, refl c |). intros [x p].
  apply sigma_eq_intro. exists p.
  destruct p. cbn. refl.
Defined.

Definition isContr_single_ended_path := lemma_3_11_8.

Lemma lemma_3_11_9_1 :
  forall (A : U) (P : A -> U),
    (forall x : A, isContr (P x)) -> sigma P ~ A.
Proof.
  unfold isContr, equiv. intros.
  exists pr1'. apply qinv_isequiv. unfold qinv.
  exists (fun x : A => (| x, pr1' (X x) |)). split.
    compute. refl.
    compute. destruct x. destruct (X x). apply sigma_eq_intro.
      exists (refl x). cbn. apply e.
Defined.

Lemma lemma_3_11_9_2 :
  forall (A : U) (P : A -> U) (c : isContr A),
    sigma P ~ P (pr1' c).
Proof.
  intros A P c. assert (S : isSet A).
    apply isProp_isSet. apply isContr_isProp. assumption.
  unfold isContr, equiv in *. destruct c as [c p]. cbn.
  exists (fun x => transport _ (inv (p (pr1' x))) (pr2' x)).
  apply qinv_isequiv. unfold qinv. cbn.
  exists (fun pc => (| c, pc |)). split.
    compute. intros. unfold isSet in S. rewrite (S _ _ _ (refl c)). refl.
    compute. destruct x. apply sigma_eq_intro; cbn.
      exists (p x). unfold isSet in S. destruct (p x). cbn. refl.
Defined.

Lemma lemma_3_11_10 :
  forall A : U,
    isProp A = forall x y : A, isContr (x = y).
Proof.
  intro. apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. intro p. assert (S : isSet A).
    apply isProp_isSet. assumption.
    unfold isContr, isProp, isSet in *. intros x y. exists (p x y).
      intro. apply S.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. unfold isContr, isProp. intros. exact (pr1' (X x y)).
  split.
    unfold homotopy. intros. apply isContr_isProp.
      do 2 (apply isContr_pi; intro). apply isContr_isContr, x.
    unfold homotopy. intros. apply isProp_isProp.
Defined.

(** ** Exercises *)

(** **** Ex. 3.1 *)

Lemma equiv_isSet :
  forall A B : U,
    A ~ B -> isSet A -> isSet B.
Proof.
  intros A B e SA. apply ua in e. rewrite <- e. assumption.
Defined.

Lemma equiv_isSet_no_univalence :
  forall A B : U,
    A ~ B -> isSet A -> isSet B.
Proof.
  unfold equiv, isSet. intros A B [f e] SA x y p q.
  apply isequiv_qinv in e. destruct e as [g [Hgf Hfg]].
  specialize (SA (g x) (g y) (ap g p) (ap g q)).
  apply (ap (ap f)) in SA. rewrite ?ap_ap in SA.
  apply funext in Hgf. apply funext in Hfg.
  assert (ap id p = ap id q).
    rewrite <- Hgf. assumption.
  rewrite ?ap_id in X. assumption.
Defined.

(** **** Ex. 3.2 *)

Definition code_sum {A B : U} (x y : A + B) : U :=
match x, y with
    | inl a, inl a' => a = a'
    | inl _, inr _ => empty
    | inr _, inl _ => empty
    | inr b, inr b' => b = b'
end.

Definition encode_sum_aux
  {A B : U} (x : A + B) : code_sum x x :=
match x with
    | inl a => refl a
    | inr b => refl b
end.

Definition encode_sum
  {A B : U} {x y : A + B} (p : x = y) : code_sum x y :=
    transport _ p (encode_sum_aux x).

Definition decode_sum
  {A B : U} {x y : A + B} (c : code_sum x y) : x = y.
Proof.
  destruct x, y; cbn in *.
    apply ap. assumption.
    destruct c.
    destruct c.
    apply ap. assumption.
Defined.

Lemma decode_encode_sum :
  forall {A B : U} {x y : A + B} (p : x = y),
    decode_sum (encode_sum p) = p.
Proof.
  destruct p, x; cbn; refl.
Defined.

Lemma encode_decode_sum :
  forall {A B : U} {x y : A + B} (c : code_sum x y),
    encode_sum (decode_sum c) = c.
Proof.
  destruct x, y, c; refl.
Defined.

Lemma sum_eq_char :
  forall (A B : U) (x y : A + B),
    (x = y) = code_sum x y.
Proof.
  intros A B x y. apply ua. unfold equiv.
  exists encode_sum.
  apply qinv_isequiv. unfold qinv.
  exists decode_sum. split.
    compute. destruct x, y; destruct x; refl.
    compute. destruct x0, x; refl.
Defined.

Lemma isSet_coprod :
  forall A B : U,
    isSet A -> isSet B -> isSet (A + B).
Proof.
  intros A B SA SB x y p q.
  assert (P : isProp (code_sum x y)).
    unfold isProp, isSet in *. destruct x, y; destruct x; cbn.
      apply SA.
      apply SB.
  rewrite <- (decode_encode_sum p), <- (decode_encode_sum q).
  unfold isProp in P. rewrite (P _ (encode_sum q)). refl.
Defined.

(** **** Ex. 3.4 *)

Lemma ex_3_4 :
  forall A : U, isProp A ~ isContr (A -> A).
Proof.
  intro. unfold equiv. esplit.
Unshelve. Focus 2.
  unfold isProp, isContr. intro p. exists id. intro. apply funext.
    intro. apply p.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve. Focus 2.
  unfold isContr, isProp. intros [g p] x y.
    pose (p1 := p (fun _ => x)). apply happly with x in p1.
    pose (p2 := p (fun _ => y)). apply happly with x in p2.
    rewrite <- p1, p2. refl.
  split.
    compute. intro. apply isProp_isContr.
    compute. intro. apply isProp_isProp.
Defined.

(** **** Ex. 3.5 *)

Lemma ex_3_5 :
  forall A : U, isProp A ~ (A -> isContr A).
Proof.
  intro. assert (isProp (A -> isContr A)).
    apply isProp_fun. apply isProp_isContr.
 unfold equiv. esplit. Unshelve. Focus 2.
    unfold isProp, isContr. intros p x. exists x. apply p.
  apply qinv_isequiv. unfold qinv. esplit. Unshelve. Focus 2.
    unfold isContr, isProp. intros H x y. destruct (H x).
      rewrite <- (e x), <- (e y). refl.
  split.
    compute. intro. apply X.
    compute. intro. apply funext. intro y. apply funext. intro z.
      destruct (x y y). destruct (x y z). refl.
Defined.

(** **** Ex. 3.7 *)

Lemma ex_3_7 :
  forall A B : U,
    isProp A -> isProp B -> ~ (A * B) -> isProp (A + B).
Proof.
  intros A B PA PB NAB x y. Search coprod.
  rewrite sum_eq_char. destruct x, y; cbn.
    apply PA.
    apply NAB. split; assumption.
    apply NAB. split; assumption.
    apply PB.
Defined.

(** **** Ex. 3.6 *)

Lemma ex_3_6 :
  forall A : U, isProp A -> isProp (A + ~ A).
Proof.
  intros A PA. apply ex_3_7.
    assumption.
    intros f g. apply funext. intro. destruct (f x).
    intros [x f]. apply f. exact x.
Defined.

(** **** Ex. 3.8 *)

Lemma ex_3_8 :
  forall (A B : U) (isequiv' : (A -> B) -> U) (f : A -> B),
    (qinv f -> isequiv' f) ->
    (isequiv' f -> qinv f) ->
    (forall e1 e2 : isequiv' f, e1 = e2) ->
      isequiv' f ~ trunc (qinv f).
Proof.
  intros * H1 H2 H3. unfold equiv.
  exists (fun e => trunc' (H2 e)).
  apply qinv_isequiv. esplit. Unshelve. Focus 2.
    apply trunc_rec.
      intros e1 e2. apply H3.
      exact H1.
    split.
      compute. intro. apply path.
      compute. intro. apply H3.
Defined.

(** **** Ex. 3.9 *)

Lemma not_A_equiv_empty :
  forall A : U,
    ~ A -> A = empty.
Proof.
  intros A H. apply ua. unfold equiv.
  exists H.
  apply qinv_isequiv. unfold qinv.
  exists (fun e : empty => match e with end).
  split; compute.
    destruct x.
    intro. destruct (H x).
Defined.

Lemma ex_3_9 :
  LEM -> sigma isProp ~ bool.
Proof.
  unfold LEM. intro LEM.
  unfold equiv. esplit.
Unshelve.
  Focus 2. destruct 1 as [P H]. exact (if LEM P H then true else false).
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. destruct 1.
    exists unit. apply isProp_unit.
    exists empty. apply isProp_empty.
  split.
    compute. destruct x.
      destruct (LEM unit).
        refl.
        cut empty.
          destruct 1.
          apply n. exact tt.
      destruct (LEM empty).
        destruct e.
        refl.
    compute. destruct x, (LEM x e).
      apply sigma_eq_intro. cbn. esplit. Unshelve.
        Focus 3. symmetry. apply ua. apply inhabited_isProp_unit.
          unfold isProp. apply e.
          exact x0.
        do 2 (apply funext; intro). assert (isProp x).
          unfold isProp. apply e.
          rewrite lemma_3_11_10 in X. destruct (X x1 x2).
            rewrite <- e0. symmetry. apply e0.
      apply sigma_eq_intro. cbn. exists (inv (not_A_equiv_empty _ n)).
        do 2 (apply funext; intro). assert (isProp x).
          unfold isProp. apply e.
          rewrite lemma_3_11_10 in X. destruct (X x0 x1).
            rewrite <- e0. symmetry. apply e0.
Defined.

(** **** Ex. 3.10 *)

(** **** Ex. 3.11 *)

Lemma ex_3_11 :
  ~ forall A : U, trunc A -> A.
Proof.
  apply not_Prop_making_functor.
    intros. apply path.
    apply trunc'. exact true.
Defined.

(** **** Ex. 3.12 *)

Lemma ex_3_12 :
  LEM -> forall A : U, trunc (trunc A -> A).
Proof.
  unfold LEM. intros LEM A.
  destruct (LEM (trunc A)).
    apply isProp_trunc.
    revert t. apply trunc_rec.
      apply isProp_trunc.
      intro. apply trunc'. intro. exact X.
    apply trunc'. intro. destruct (n X).
Defined.

(** **** Ex. 3.13 *)

Lemma ex_3_13_aux :
  (forall A : U, A + ~ A) -> PNE.
Proof.
  unfold PNE. intros LEM X Y SX SY f.
  apply trunc'. intro.
  destruct (LEM (Y x)).
    exact y.
    cut empty.
      destruct 1.
      specialize (f x). revert f. apply trunc_rec.
        apply isProp_empty.
        intro. apply n. assumption.
Defined.

Lemma ex_3_13 :
  (forall A : U, A + ~ A) -> AC.
Proof.
  intros. rewrite AC_PNE. apply ex_3_13_aux. assumption.
Defined.

(** **** Ex. 3.14 *)

Definition DN_rec : U :=
  forall A B : U, isProp B -> (A -> B) -> ~ ~ A -> B.

Search trunc.

Lemma ex_3_14 :
  LEM -> {R : DN_rec &
            forall (A B : U) (H : isProp B) (f : A -> B) (x : A),
              R A B H f (fun g => g x) = f x}.
Proof.
  unfold LEM, DN_rec. intro LEM. esplit.
Unshelve.
  Focus 2. intros A B PB f H.
    destruct (LEM B).
      assumption.
      exact b.
      cut empty.
        destruct 1.
        apply H. intro. apply n, f. assumption.
  intros A B PB f x. cbn. destruct (LEM B PB).
    apply PB.
    destruct (n (f x)).
Defined.

Lemma ex_3_14' :
  LEM -> forall A : U, (~ ~ A) = trunc A.
Proof.
  unfold LEM. intros LEM A.
  apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. intro. destruct (LEM (trunc A)).
    apply isProp_trunc.
    assumption.
    cut empty.
      destruct 1.
      apply X. intro. apply n, trunc', X0.
  cbn. apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. do 2 intro. revert X. apply trunc_rec.
    apply isProp_empty.
    intro. apply X0. assumption.
  split.
    compute. intro. destruct (LEM (trunc A)).
      apply path.
      apply path.
    compute. intro. apply funext. intro. destruct (x x0).
Defined.

(** **** Ex. 3.15 TODO *)

(** **** Ex. 3.16 *)

Lemma LEM_DNE :
  LEM -> DNE.
Proof.
  unfold LEM, DNE. intros LEM P PP H.
  destruct (LEM P).
    apply PP.
    assumption.
    cut empty.
      destruct 1.
      apply H. assumption.
Defined.

Lemma ex_3_16 :
  LEM ->
    forall (X : U) (Y : X -> U),
      isSet X -> (forall x : X, isProp (Y x)) ->
        (forall x : X, ~ ~ Y x) = ~ ~ forall x : X, Y x.
Proof.
  unfold LEM. intros LEM X Y SX PY.
  apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. intros f H. apply H. intro. apply (LEM_DNE LEM).
    apply PY.
    apply f.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. intros H x HY. apply HY. apply (LEM_DNE LEM) in H.
    apply H.
    apply isProp_pi. assumption.
  split.
    compute. intro. apply funext. intro. destruct (x x0).
    compute. intro. apply funext. intro. apply funext. intro.
      destruct (x x0 x1).
Defined.

Definition AC_neg : U :=
  forall (X : U) (Y : X -> U),
    isSet X -> (forall x : X, isSet (Y x)) ->
      (forall x : X, ~ ~ Y x) = ~ ~ forall x : X, Y x.

Lemma ex_3_16'' :
  LEM -> AC_neg -> AC.
Proof.
  rewrite AC_PNE.
  unfold LEM, AC_neg, PNE.
  intros LEM AC_neg X Y SX SY f.
  rewrite <- (ex_3_14' LEM). rewrite <- AC_neg; try assumption.
  intro. rewrite (ex_3_14' LEM). apply f.
Defined.

(** **** Ex. 3.17 *)

Lemma ex_3_17 :
  forall {A : U} {B : trunc A -> U},
    (forall x : trunc A, isProp (B x)) ->
    (forall x : A, B (trunc' x)) ->
      forall x : trunc A, B x.
Proof.
  intros A B PB H.
  intro. Check @trunc_rec. eapply trunc_rec.
    apply PB.
    intro. specialize (H X). assert (p : trunc' X = x).
      apply path.
      rewrite <- p. assumption.
    assumption.
Defined.

(** **** Ex. 3.18 *)

Lemma DNE_LEM :
  DNE -> LEM.
Proof.
  unfold DNE, LEM. intros DNE P PP.
  apply DNE.
    apply ex_3_6. assumption.
    intro. assert ((~ P) * ~ ~ P).
      split; intro.
        apply X. left. assumption.
        apply X. right. assumption.
      destruct X0. apply n0. assumption.
Defined.

Lemma isProp_DNE : isProp DNE.
Proof.
  unfold isProp, DNE. intros.
  apply funext. intro P. apply funext. intro PP. apply funext. intro H.
  apply PP.
Defined.

Lemma isProp_LEM : isProp LEM.
Proof.
  unfold isProp, LEM. intros.
  apply funext. intro P. apply funext. intro PP.
  apply ex_3_6. assumption.
Defined.

Lemma LEM_is_DNE : LEM = DNE.
Proof.
  apply ua. unfold equiv.
  exists (LEM_DNE).
  apply qinv_isequiv. unfold qinv.
  exists (DNE_LEM).
  split.
    unfold homotopy. intro. apply isProp_DNE.
    unfold homotopy. intro. apply isProp_LEM.
Defined.

(** **** Ex. 3.20 *)

(** See lemma_3_11_9 *)

(** **** Ex. 3.21 *)

Lemma iff_equiv :
  forall P Q : U,
    isProp P -> isProp Q -> (P -> Q) -> (Q -> P) -> P ~ Q.
Proof.
  intros P Q HP HQ PQ QP.
  unfold equiv.
  exists PQ. apply qinv_isequiv. unfold qinv. exists QP.
  split.
    unfold homotopy. intro. apply HQ.
    unfold homotopy. intro. apply HP.
Defined.

Lemma isProp_eq_aux :
  forall P : U,
    isProp P -> forall (x y : P) (p : x = y), p = transport _ p (refl x).
Proof.
  destruct p. cbn. refl.
Defined.

Lemma isProp_eq :
  forall P : U,
    isProp P -> forall x y : P, isProp (x = y).
Proof.
  intros. pose isProp_isSet. unfold isProp, isSet in *.
  apply i. assumption.
Defined.

Lemma ex_3_21_aux :
  forall P : U, isProp (P ~ trunc P).
Proof.
  unfold isProp. intros P x y.
  assert (P = trunc P).
    apply ua. assumption.
  assert (PP : isProp P).
    rewrite X. apply isProp_trunc.
  destruct x as [x [[x1 Hx1] [x2 Hx2]]].
  destruct y as [y [[y1 Hy1] [y2 Hy2]]].
  destruct X.
  apply sigma_eq_intro. cbn. esplit.
Unshelve.
  Focus 2. apply funext. intro. apply PP.
  compute. destruct _. apply prod_eq_intro. cbn. split.
    destruct s as [s1 Hs1]. apply sigma_eq_intro. cbn. esplit. Unshelve.
      Focus 3. apply funext. intro. apply PP.
      apply funext. intro. apply (isProp_eq _ PP).
    destruct s0 as [s1 Hs1]. apply sigma_eq_intro. cbn. esplit. Unshelve.
      Focus 2. apply funext. intro. apply PP.
      apply funext. intro. apply (isProp_eq _ PP).
Defined.

Lemma ex_3_21 :
  forall P : U, isProp P ~ (P ~ trunc P).
Proof.
  intro. apply iff_equiv.
    apply isProp_isProp.
    apply ex_3_21_aux.
    intro. apply iff_equiv.
      assumption.
      apply isProp_trunc.
      apply trunc'.
      apply trunc_rec.
        assumption.
        intro. assumption.
    intro. apply ua in X. rewrite X. apply isProp_trunc.
Defined.

(** **** Ex. 3.22 *)

Fixpoint Fin' (n : N) : U :=
match n with
    | 0 => empty
    | S n' => unit + Fin' n'
end.

Definition AC_Fin' : U :=
  forall (n : N) (A : Fin' n -> U) (P : forall x : Fin' n, A x -> U),
    (forall x : Fin' n, isSet (A x)) ->
    (forall (x : Fin' n) (a : A x), isProp (P x a)) ->
    (forall x : Fin' n, trunc {a : A x & P x a}) ->
      trunc {f : forall x : Fin' n, A x & forall x : Fin' n, P x (f x)}.

Lemma ex_3_22 : AC_Fin'.
Proof.
  unfold AC_Fin'.
  induction n as [| n']; cbn; intros A P SA PP f.
    apply trunc'. esplit. Unshelve. 1,3: destruct x.
    rewrite pi_sum in *.
      destruct SA as [SA1 SA2], PP as [PP1 PP2], f as [f1 f2].
      pose (B := fun x => A (inr x)).
      pose (P' := fun x => P (inr x)).
      specialize (IHn' B P' SA2 PP2 f2). revert IHn'.
      apply trunc_rec.
        apply isProp_trunc.
        destruct 1 as [g H]. specialize (f1 tt). revert f1. apply trunc_rec.
          apply isProp_trunc.
          destruct 1 as [a1 a2]. apply trunc'. esplit.
Unshelve.
  Focus 2.
    destruct x as [[] | x].
      exact a1.
      apply g.
    destruct x as [[] | x].
      exact a2.
      apply H.
Defined.

(** **** Ex. 3.23 *)

Inductive le : N -> N -> U :=
    | le_0 : forall n : N, le 0 n
    | le_S_S : forall n m : N, le n m -> le (S n) (S m).

Infix "<=" := le (at level 50).

Fixpoint code_le (n m : N) : U :=
match n, m with
    | 0, _ => unit
    | S _, 0 => empty
    | S n', S m' => code_le n' m'
end.

Lemma encode_le :
  forall {n m : N} (p : n <= m), code_le n m.
Proof.
  induction 1; cbn.
    exact tt.
    assumption.
Defined.

Fixpoint decode_le {n m : N} : code_le n m -> n <= m :=
match n, m with
    | 0, _ => fun _ => le_0 m
    | S _ , 0 => fun c => match c with end
    | S n', S m' => fun c => le_S_S n' m' (@decode_le n' m' c)
end.

Lemma decode_encode_le :
  forall {n m : N} (p : n <= m),
    decode_le (encode_le p) = p.
Proof.
  induction p.
    cbn. refl.
    compute in *; rewrite IHp; clear IHp. refl.
Defined.

Lemma isProp_code_le :
  forall n m : N, isProp (code_le n m).
Proof.
  unfold isProp. induction n as [| n'], m as [| m']; cbn; intros.
    destruct x, y. refl.
    destruct x, y. refl.
    destruct x.
    apply IHn'.
Defined.

Lemma isProp_le :
  forall n m : N, isProp (le n m).
Proof.
  unfold isProp. intros.
  rewrite <- (decode_encode_le x), <- (decode_encode_le y).
  rewrite (isProp_code_le _ _ (encode_le x) (encode_le y)).
  refl.
Defined.

Lemma le_refl :
  forall n : N, n <= n.
Proof.
  induction n as [| n'].
    constructor.
    apply le_S_S. assumption.
Defined.

Lemma le_wasym :
  forall n m : N, n <= m -> m <= n -> n = m.
Proof.
  induction 1; intro.
    apply encode_le in H. destruct n; cbn in H.
      refl.
      destruct H.
    apply encode_le in H0. cbn in H0. apply decode_le in H0.
      apply ap. apply IHle. assumption.
Defined.

Lemma le_trans :
  forall a b c : N, a <= b -> b <= c -> a <= c.
Proof.
  intros a b c H. revert c. induction H; intros.
    constructor.
    apply encode_le in H0. cbn in H0. destruct c as [| c'].
      destruct H0.
      apply le_S_S, IHle. apply decode_le in H0. assumption.
Defined.

Lemma le_S :
  forall n m : N, n <= m -> n <= S m.
Proof.
  induction 1; constructor; assumption.
Defined.

Lemma le_not_lt :
  forall n m : N,
    n <= m = ~ S m <= n.
Proof.
  intros. apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. induction 1; intro.
    apply encode_le in H. cbn in H. assumption.
    apply encode_le in H0. cbn in H0. destruct n; cbn in H0.
      assumption.
      apply IHle. apply le_S_S. apply decode_le. assumption.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. revert m. induction n as [| n']; intros.
    apply le_0.
    destruct m as [| m'].
      cut empty.
        destruct 1.
        apply H. apply decode_le. cbn. exact tt.
      apply le_S_S. apply IHn'. intro. apply H.
        apply le_S_S. assumption.
  split.
    compute. intro. apply funext. intro. destruct (x x0).
    compute. intro. apply isProp_le.
Defined.

Lemma search :
  forall (P : N -> U) (dec : forall n : N, P n + ~ P n) (n : N),
    (forall m : N, S m <= n -> ~ P m) +
    {m : N & P m * (S m <= n) * forall m' : N, P m' -> m <= m'}.
Proof.
  induction n as [| n'].
    left. do 3 intro. apply encode_le in H. cbn in H. assumption.
    destruct IHn' as [H | (m & Pm & H1 & H2)].
      destruct (dec n').
        right. exists n'. repeat split.
          assumption.
          apply le_refl.
          intros. rewrite le_not_lt. intro. specialize (H _ H0).
            contradiction.
        left. do 3 intro. eapply H.
          2: eassumption.
          rewrite le_not_lt. intro.
            apply encode_le in H0. apply encode_le in H1. cbn in *.
            apply decode_le in H0. apply decode_le in H1. assert (p : n' = m).
              apply le_wasym; assumption.
              apply n. rewrite p. assumption.
      right. exists m. repeat split.
        assumption.
        apply le_S. assumption.
        assumption.
Defined.

Definition goal (P : N -> U) : U :=
  sigma (fun n : N => trunc (P n * forall m : N, P m -> n <= m)).

Lemma isProp_goal :
  forall P : N -> U, isProp (goal P).
Proof.
  unfold goal, isProp. intros. apply sigma_eq_intro.
  destruct x as [x Hx], y as [y Hy]. cbn.
  assert (p : x = y).
    revert Hx. apply trunc_rec.
      unfold isProp. apply isSet_N.
      intros [Px Hx]. revert Hy. apply trunc_rec.
        unfold isProp. apply isSet_N.
        intros [Py Hy]. specialize (Hx _ Py). specialize (Hy _ Px).
          apply (le_wasym _ _ Hx Hy).
  exists p. destruct p. cbn. apply isProp_trunc.
Defined.

Lemma ex_3_23_aux :
  forall P : N -> U,
    (forall n : N, P n + ~ P n) ->
      trunc {n : N & P n} -> goal P.
Proof.
  intros P dec. apply trunc_rec.
    apply isProp_goal.
    intros [n Pn]. unfold goal.
      destruct (search P dec n) as [H | (m & H1 & H2 & H3)].
        exists n. apply trunc'. split.
          assumption.
          intros. rewrite le_not_lt. intro. apply (H _ H0). assumption.
        exists m. apply trunc'. split.
          assumption.
          assumption.
Defined.

Lemma ex_3_23 :
  forall P : N -> U,
    (forall n : N, P n + ~ P n) ->
      trunc {n : N & P n} -> {n : N & P n}.
Proof.
  intros P dec H. destruct (ex_3_23_aux P dec H) as [n Hn].
  exists n. destruct (dec n).
    assumption.
    cut empty.
      destruct 1.
      revert Hn. apply trunc_rec.
        apply isProp_empty.
        destruct 1. contradiction.
Defined.

(** **** Ex. 1.14 MOVED *)

(** Because both endpoints of the path are fixed. For a counterexample,
    see *)

Lemma negb_not_refl :
  ua negb_equiv <> refl bool.
Proof.
  intro. assert (transport (fun A => A) (refl bool) true = false).
    destruct X. rewrite transport_ua. cbn. refl.
  cbn in X0. apply neq_false_true. apply inv. assumption.
Defined.

(** ** My own stuff *)

Module term1.

Inductive term (Var : U) : U :=
    | Var : Var -> term Var
    | Lam : (Var -> term Var) -> term Var
    | App : term Var -> term Var -> term Var.

Arguments Var {Var} _.
Arguments Lam {Var} _.
Arguments App {Var} _ _.

Fixpoint code_term {Var : U} (t1 t2 : term Var) : U :=
match t1, t2 with
    | Var v1, Var v2 => v1 = v2
    | Lam f, Lam g => forall v : Var, code_term (f v) (g v)
    | App t11 t12, App t21 t22 => code_term t11 t21 * code_term t12 t22
    | _, _ => empty
end.

Lemma isProp_code_term :
  forall (Var : U) (t1 t2 : term Var),
    (forall v1 v2 : Var, isProp (v1 = v2)) -> isProp (code_term t1 t2).
Proof.
  induction t1, t2; cbn; intros; try (apply isProp_empty).
    apply X.
    unfold isProp. intros f g. apply funext. intro v.
      apply X. assumption.
    apply isProp_prod.
      apply IHt1_1. assumption.
      apply IHt1_2. assumption.
Defined.

Lemma isProp_code_term' :
  forall (Var : U) (t1 t2 : term Var),
    isSet Var -> isProp (code_term t1 t2).
Proof.
  intros. apply isProp_code_term. unfold isProp. apply X.
Defined.

Definition encode_term_aux :
  forall {Var : U} (t : term Var), code_term t t.
Proof.
  induction t; cbn.
    refl.
    assumption.
    split; assumption.
Defined.

Fixpoint encode_term_aux'
  {Var : U} (t : term Var) : code_term t t :=
match t with
    | Var v => refl v
    | Lam f => fun v => encode_term_aux' (f v)
    | App t1 t2 => (encode_term_aux' t1, encode_term_aux' t2)
end.

Definition encode_term
  {Var : U} {t1 t2 : term Var} (p : t1 = t2) : code_term t1 t2 :=
    transport _ p (encode_term_aux' t1).

Definition ap2
  {A B C : U} (f : A -> B -> C)
  {a1 a2 : A} {b1 b2 : B}
  (p : a1 = a2) (q : b1 = b2) : f a1 b1 = f a2 b2.
Proof.
  destruct p, q. refl.
Defined.

Lemma ap2_refl :
  forall 
    {A B C : U} (f : A -> B -> C) {a : A} {b : B},
      ap2 f (refl a) (refl b) = refl (f a b).
Proof. refl. Defined.

Definition decode_term
  {Var : U} {t1 t2 : term Var} (c : code_term t1 t2) : t1 = t2.
Proof.
  revert t2 c.
  induction t1; destruct t2; cbn; intros; try (destruct c; fail).
    apply ap. assumption.
    apply ap. apply funext. intro v. apply X. apply c.
    destruct c as [c1 c2]. apply ap2.
      apply IHt1_1. assumption.
      apply IHt1_2. assumption.
Defined.

Lemma transport_refl :
  forall (A : U) (P : A -> U) (x : A) (y : P x),
    transport _ (refl x) y = y.
Proof. refl. Defined.

Lemma decode_encode_term :
  forall (Var : U) (t1 t2 : term Var) (p : t1 = t2),
    decode_term (encode_term p) = p.
Proof.
  destruct p. induction t1; cbn.
    refl.
    rewrite <- ap_refl, refl_pi. apply ap, ap, funext.
      intro v. apply X.
    rewrite <- ap2_refl. apply ap2.
      apply IHt1_1.
      apply IHt1_2.
Defined.

Lemma encode_decode_term :
  forall (Var : U) (t1 t2 : term Var),
    isSet Var -> forall c : code_term t1 t2,
      encode_term (decode_term c) = c.
Proof.
  intros. apply isProp_code_term'. assumption.
Defined.

Lemma encode_decode_term' :
  forall (Var : U) (t1 t2 : term Var) (c : code_term t1 t2),
    encode_term (decode_term c) = c.
Proof.
  induction t1; destruct t2; intro c; try (destruct c; fail).
    destruct c. cbn. refl.
    cbn in c. apply funext. intro v.
Focus 2. cbn.
      cbn. unfold ap2.
Abort.

Lemma term_isSet :
  forall Var : U, isSet Var -> isSet (term Var).
Proof.
  intros Var SVar t1 t2 p q.
  rewrite <- (decode_encode_term _ _ _ p), <- (decode_encode_term _ _ _ q).
  apply ap. apply isProp_code_term'. assumption.
Defined.

Lemma term_eq_char :
  forall (Var : U) (t1 t2 : term Var),
    isSet Var -> (t1 = t2) = code_term t1 t2.
Proof.
  intros Var t1 t2 SVar. apply ua. unfold equiv.
  exists encode_term.
  apply qinv_isequiv. unfold qinv.
  exists decode_term. unfold comp; split; intro.
    apply encode_decode_term; assumption.
    apply decode_encode_term; assumption.
Defined.

End term1.

(** * 4 Equivalences *)

Lemma sigma_prod :
  forall A B : U,
    {x : A & B} = A * B.
Proof.
  intros. apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. destruct 1 as [a b]. split; assumption.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. destruct 1 as [a b]. exists a. assumption.
  split; compute; destruct x; refl.
Defined.

Definition qinv' {A B : U} (f : A -> B) : U :=
  {g : B -> A & (comp g f = id) * (comp f g = id)}.

Lemma qinv_qinv' : @qinv = @qinv'.
Proof.
  apply funext. intro A. apply funext. intro B. apply funext. intro f.
  apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. destruct 1 as [g [H1 H2]]. unfold qinv'. exists g. split.
    apply funext. assumption.
    apply funext. assumption.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. destruct 1 as [g [p q]]. exists g. split; intro.
    apply happly with x in p. assumption.
    apply happly with x in q. assumption.
  split; unfold homotopy.
    destruct x as [g [p q]]. cbn. apply sigma_eq_intro. cbn.
      exists (refl g). cbn. rewrite <- 2!funext_happly. refl.
    destruct x as [g [H1 H2]]. cbn. apply sigma_eq_intro. cbn.
      exists (refl g). cbn. rewrite 2!happly_funext. refl.
Defined.

Lemma lemma_4_1_1 :
  forall (A B : U) (f : A -> B) (g : qinv f),
    qinv f = forall x : A, x = x.
Proof.
  intros. assert (e : isequiv f).
    apply qinv_isequiv. assumption.
  rewrite qinv_qinv' in *.
  pose (p := (| f, e |) : A ~ B).
  assert (idtoeqv (ua p) = p).
    apply idtoeqv_ua'.
  destruct (ua p). compute in X. clear p.
  apply sigma_eq_elim in X. cbn in X.
  destruct X as [p q]. rewrite <- p. unfold qinv'.
  rewrite sigma_prod_assoc.
  assert ((forall x : A, x = x) = (@id A = @id A)).
    apply ua. unfold equiv. esplit.
Abort.

Lemma lemma_4_1_1 :
  forall (A B : U) (f : A -> B) (X : qinv f),
    qinv f = forall x : A, x = x.
Proof.
  intros. apply ua. unfold equiv. esplit.
Unshelve.
  Focus 2. destruct 1 as [g [H1 H2]]. intro.
    unfold homotopy, comp, id in *.
    pose (p1 := H2 x).
    pose (p2 := ap f p1).
    pose (p3 := cat (inv (H1 (f x))) p2).
    pose (p4 := ap g p3).
    pose (p5 := cat (inv (H2 x)) (cat p4 (H2 x))).
    exact p5.
  apply qinv_isequiv. unfold qinv. esplit.
Unshelve.
  Focus 2. intro H. destruct X as [g [p q]]. exists g.
    unfold homotopy, comp, id in *. split; intro.
      apply p.
      apply q.
  split.
    unfold homotopy. intro. apply funext. intro. unfold comp.
      destruct X as [g [H1 H2]]. unfold homotopy in *.
      rewrite ap_cat. rewrite ap_inv. rewrite ap_ap.
        assert (comp f g = id).
          apply funext. assumption.
Abort.