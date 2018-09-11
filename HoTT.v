(* Required in 8.8.1 to make Ltac work with the -noinit option. *)
Declare ML Module "ltac_plugin".
Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

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
  (prod A B) (at level 40, left associativity).

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

(** * 1.9 The Nural numbers *)

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

(*Definition le (n m : N) : U :=
  {k : N & add n k = m}.

Definition lt (n m : N) : U :=
  {k : N & add n (S k) = m}.*)

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

Definition comp {A B C : U} (f : A -> B) (g : B -> C) : A -> C :=
  fun x : A => g (f x).

Lemma comp_assoc :
  forall (A B C D : U) (f : A -> B) (g : B -> C) (h : C -> D),
    comp (comp f g) h = comp f (comp g h).
Proof. refl. Defined.

(** **** Ex. 1.4 *)
Fixpoint iter (C : Type) (c0 : C) (cs : C -> C) (n : N) : C :=
match n with
    | 0 => c0
    | S n' => cs (iter C c0 cs n')
end.

Definition pred (n : N) : N :=
match n with
    | 0 => 0
    | S n' => n'
end.

Definition rec (C : Type) (c0 : C) (cs : N -> C -> C) (n : N) : C :=
  iter
    (N -> C -> C)
    (fun _ _ => c0)
    (fun f k c => cs (pred k) (f (pred k) c))
    n
    n
    c0.

Lemma rec_spec_0 :
  forall (C : Type) (c0 : C) (cs : N -> C -> C),
    rec C c0 cs 0 = c0.
Proof.
  reflexivity.
Defined.

Lemma rec_spec_1 :
  forall (C : Type) (c0 : C) (cs : N -> C -> C) (n : N),
    rec C c0 cs (S n) = cs n (rec C c0 cs n).
Proof.
  intros. unfold rec. cbn.
  reflexivity.
Defined.

(* Ex. 1.9 *)
Inductive Fin : N -> Type :=
    | Fin_1 : Fin (S 0)
    | Fin_SS : forall n : N, Fin (S n) -> Fin (S (S n)).

Fixpoint fmax (n : N) : Fin (S n) :=
match n with
    | 0 => Fin_1
    | S n' => Fin_SS n' (fmax n')
end.

Notation "1" := (S 0).

(* Ex. 1.10 *)
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

Goal forall m n : N, ack m n = ack' m n.
Proof.
  induction m as [| m']; cbn.
    refl.
    induction n as [| n']; cbn.
      rewrite <- IHm'. refl.
      rewrite <- IHm', <- IHn'. refl.
Defined.

(* Ex. 1.11 *)
Goal forall A : Prop, ~ ~ ~ A -> ~ A.
Proof.
  intros. intro. apply X. intro. apply X0. assumption.
Defined.

Definition sum' A B := {b : bool & if b then A else B}.

Check sigma.

Definition inl' {A B : Type} (a : A) : sum' A B := (| true, a |).
Definition inr' {A B : Type} (b : B) : sum' A B := (| false, b |).

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

Definition loopspace (A : Pointed) : Pointed :=
match A with
    | (| _, a |) => (| a = a, refl a |)
end.

Fixpoint nfold_loopspace (n : N) (A : Pointed) : Pointed :=
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
Lemma homotopy_Nural :
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
    pose (e := homotopy_Nural A A f id H (f x) x (H x)).
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

(* In the book, elimiNion rules for products are [ap pr1] and [ap pr2]. *)
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

Definition idtoeqv {A B : Type} (p : A = B) : equiv A B.
Proof.
  unfold equiv. exists (transport _ p).
  destruct p. cbn. apply isequiv_id.
Defined.

Axiom ua : forall {A B : U} (e : equiv A B), @eq U A B.

Definition apply_equiv {A B : Type} (e : A ~ B) : A -> B := pr1' e.
Coercion apply_equiv : equiv >-> Funclass.

Axiom idtoeqv_ua :
  forall {A B : U} (e : A ~ B) (x : A),
    idtoeqv (ua e) x = e x.

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
  rewrite (ua_idtoeqv (ua f)).
  rewrite (ua_idtoeqv (ua g)). Search transport.
  assert (forall (u : A),
    idtoeqv (cat (ua (idtoeqv (ua f))) (ua (idtoeqv (ua g)))) u =
    idtoeqv (ua (equiv_trans A B C f g)) u).
      intro. rewrite ?idtoeqv_ua. cbn.
        rewrite <- transport_cat, ?transport_ua, ?idtoeqv_ua.
          compute.
Admitted.

(** ** 2.11 Identity types *)

Theorem ap_isequiv :
  forall (A B : U) (f : A -> B) (x y : A),
    isequiv f -> isequiv (@ap A B f x y).
Proof.
  intros. apply qinv_isequiv. apply isequiv_qinv in X.
  unfold qinv in *. destruct X as [g [H1 H2]].
  eapply (| _, _ |).
Unshelve.
  intros. apply (cat (inv (H2 x)) (cat (ap g X) (H2 y))).
  cbn. unfold homotopy, comp, id in *. hsplit; intros.
    rewrite !ap_cat. rewrite !ap_inv. rewrite !ap_ap.
      Check homotopy_Nural.
    Focus 2. destruct x0. rewrite ap_refl, cat_refl_l, cat_inv_l. refl.
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
  destruct b1, b2; cbn in c.
    refl.
    destruct c.
    destruct c.
    refl.
Defined.

Lemma decode_encode_bool :
  forall {b1 b2 : bool} (p : b1 = b2),
    decode_bool (encode_bool p) = p.
Proof.
  destruct p. destruct b1; cbn.
    1-2: refl.
Defined.

Lemma isSet_bool : isSet bool.
Proof.
  unfold isSet. intros.
  rewrite <- (decode_encode_bool p), <- (decode_encode_bool q).
  destruct p, x; cbn.
    1-2: refl.
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

Definition const {A : U} (x y : A) : A := x.

Lemma neq_false_true : ~ false = true.
Proof.
  intro p.
  exact
  (@transport _ (fun b : bool => if b then empty else unit) _ _ p tt).
Defined.

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

(** WUT: a little test *)

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

Print encode_term_aux.
Print encode_term_aux'.

Definition encode_term
  {Var : U} {t1 t2 : term Var} (p : t1 = t2) : code_term t1 t2 :=
    transport _ p (encode_term_aux' t1).

(*Fixpoint decode_term
  {Var : U} {t1 t2 : term Var} (c : code_term t1 t2) : t1 = t2 :=
match t1, t2 with
    | Var v1, Var v2 => ap Var c
    | Lam f, Lam g
*)

Definition decode_term
  {Var : U} {t1 t2 : term Var} (c : code_term t1 t2) : t1 = t2.
Proof.
  revert t2 c.
  induction t1; destruct t2; cbn; intros; try (destruct c; fail).
    apply ap. assumption. Show Proof.
    apply ap. apply funext. intro v. apply X. apply c.
    destruct c as [c1 c2].
      specialize (IHt1_1 _ c1); specialize (IHt1_2 _ c2).
      destruct IHt1_1, IHt1_2. refl.
(*Restart.
  revert t1 t2 c. fix IH 1.
  destruct t1, t2; cbn; try destruct 1.*)
Defined.

Lemma transport_refl :
  forall (A : U) (P : A -> U) (x : A) (y : P x),
    transport _ (refl x) y = y.
Proof. refl. Defined.

Lemma decode_encode_term :
  forall (Var : U) (t1 t2 : term Var) (p : t1 = t2),
    decode_term (encode_term p) = p.
Proof.
  destruct p.
  induction t1.
    cbn. refl.
    unfold encode_term. rewrite transport_refl.
      compute.
Admitted.

Lemma code_term_isProp :
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

Lemma term_isSet :
  forall Var : U, isSet Var -> isSet (term Var).
Proof.
  unfold isSet. intros.
  rewrite <- (decode_encode_term _ _ _ p), <- (decode_encode_term _ _ _ q).
  rewrite (code_term_isProp _ x y X (encode_term p) (encode_term q)).
  refl.
Defined.

(** ** 3.7 Propositional truncation *)

Axiom trunc : U -> U.
Axiom trunc' : forall {A : U}, A -> trunc A.
Axiom path : forall {A : U} (x y : trunc A), x = y.

Axiom trunc_rec :
  forall {A B : U},
    isProp B -> (A -> B) -> trunc A -> B.

(*Axiom trunc_ind :
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
      admit. (* TODO: isSet_sigma *)
    specialize (PNS X0 f). revert PNS. apply trunc_rec.
      apply isProp_trunc.
      intro. apply trunc'. exists (fun x : X => pr1' (X1 x)). intro.
        destruct (X1 x). cbn. assumption.
  }
  split.
    compute. intros. repeat (apply funext; intro). apply path.
    compute. intros. repeat (apply funext; intro). apply path.
Admitted.

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

Lemma isContr_single_ended_path :
  forall (A : U) (c : A),
    isContr (sigma (fun x : A => c = x)).
Proof.
  unfold isContr. intros.
  exists (| c, refl c |). intros [x p].
  apply sigma_eq_intro. exists p.
  destruct p. cbn. refl.
Defined.

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

(** **** Ex. 3.23 *)

(*Inductive le (n : N) : N -> U :=
    | le_refl : le n n
    | le_S_r : forall m : N, le n m -> le n (S m).
*)

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


(*
match n, m with
    | 0, _ => tt
    | S _, 0 => match p with end
    | S n', S m' => encode_le n' m'
end.
*)
(*
Lemma decode_le :
  forall {n m : N} (c : code_le n m), n <= m.
Proof.
  induction n as [| n']; cbn; intros.
    constructor.
    destruct m as [| m'].
      destruct c.
      constructor. apply IHn'. assumption.
Defined. Print decode_le.
*)

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

Fixpoint search
  (P : N -> U) (dec : forall n : N, P n + ~ P n)
  (n : N) (acc : N) (Hacc : P acc) : sigma P :=
match n with
    | 0 =>
        match dec 0 with
            | inl H => (| 0, H |)
            | _ => (| acc, Hacc |)
        end
    | S n' =>
        match dec n with
            | inl H => search P dec n' n H
            | _ => search P dec n' acc Hacc
        end
end.

Fixpoint search'
  (P : N -> U) (dec : forall n : N, P n + ~ P n)
  (n : N) (acc : N) : N :=
match n with
    | 0 =>
        match dec 0 with
            | inl H => 0
            | _ => acc
        end
    | S n' =>
        match dec n' with
            | inl H => search' P dec n' n'
            | _ => search' P dec n' acc
        end
end.

Fixpoint search2 :
  (P : N -> U) (dec : forall n : N, P n + ~ P n)
  (n : N) (acc : N) : unit + N :=
match n with
    | 0 =>
        match dec 0 with
            | inl H => inr 0
            | _ => inl tt
        end
    | S n' =>
        match dec n' with
            | inl H => search' P dec n' n'
            | _ => search' P dec n' acc
        end
end.

Lemma search'_aux_1 :
  forall (P : N -> U) (dec : forall n : N, P n + ~ P n) (n m : N),
    P m -> P (search' P dec n m).
Proof.
  induction n as [| n']; cbn; intros.
    destruct (dec 0).
      assumption.
      assumption.
    destruct (dec n').
      apply IHn'. assumption.
      apply IHn'. assumption.
Defined.

Lemma search'_aux_2 :
  forall (P : N -> U) (dec : forall n : N, P n + ~ P n) (n acc m : N),
    n <= acc -> acc <= m -> P acc -> P m -> search' P dec n acc <= m.
Proof.
  induction n as [| n']; cbn; intros.
    destruct (dec 0).
      constructor.
      assumption.
    destruct (dec n').
      apply IHn'; try assumption.
        admit.
        admit.
      apply IHn'; try assumption. admit.
Admitted.

Lemma ex_3_23 :
  forall P : N -> U,
    (forall n : N, P n + ~ P n) ->
      trunc (sigma P) -> goal P.
Proof.
  intros P dec. apply trunc_rec.
    apply isProp_goal.
    intros [n Pn]. unfold goal.
      exists (search' P dec n n). apply trunc'. split.
        apply search'_aux_1. assumption.
        clear Pn. generalize n at 2. induction n as [| n']; cbn; intros.
          destruct (dec 0). constructor.
Abort.

(** * 4 Equivalences *)

