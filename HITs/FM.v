Require Import List.
Import ListNotations.

From HoTT Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

Module FreeMon.

Private Inductive FM (A : Type) : Type :=
    | i  : A -> FM A
    | op : FM A -> FM A -> FM A
    | id : FM A.

Arguments i  {A} _.
Arguments op {A} _ _.
Arguments id {A}.

Axiom op_id_l : forall {A : Type} (y : FM A), op id y = y.
Axiom op_id_r : forall {A : Type} (x : FM A), op x id = x.
Axiom op_assoc : forall {A : Type} (x y z : FM A), op (op x y) z = op x (op y z).

Fixpoint FM_rec
  {A P : Type}
  (i' : A -> P)
  (op' : P -> P -> P)
  (id' : P)
  (op_id_l' : forall y : P, op' id' y = y)
  (op_id_r' : forall x : P, op' x id' = x)
  (op_assoc' : forall x y z : P, op' (op' x y) z = op' x (op' y z))
  (x : FM A) : P :=
match x with
    | i a => i' a
    | op a b => op' (FM_rec i' op' id' op_id_l' op_id_r' op_assoc' a)
                    (FM_rec i' op' id' op_id_l' op_id_r' op_assoc' b)
    | id => id'
end.

Axiom FM_rec_op_id_l :
  forall
    {A P : Type}
    (i' : A -> P)
    (op' : P -> P -> P)
    (id' : P)
    (op_id_l' : forall y : P, op' id' y = y)
    (op_id_r' : forall x : P, op' x id' = x)
    (op_assoc' : forall x y z : P, op' (op' x y) z = op' x (op' y z))
    (y : FM A),
      ap (FM_rec i' op' id' op_id_l' op_id_r' op_assoc') (op_id_l y)
        =
      op_id_l' (FM_rec i' op' id' op_id_l' op_id_r' op_assoc' y).

Axiom FM_rec_op_id_r :
  forall
    {A P : Type}
    (i' : A -> P)
    (op' : P -> P -> P)
    (id' : P)
    (op_id_l' : forall y : P, op' id' y = y)
    (op_id_r' : forall x : P, op' x id' = x)
    (op_assoc' : forall x y z : P, op' (op' x y) z = op' x (op' y z))
    (x : FM A),
      ap (FM_rec i' op' id' op_id_l' op_id_r' op_assoc') (op_id_r x)
        =
      op_id_r' (FM_rec i' op' id' op_id_l' op_id_r' op_assoc' x).

Axiom FM_rec_op_assoc :
  forall
    {A P : Type}
    (i' : A -> P)
    (op' : P -> P -> P)
    (id' : P)
    (op_id_l' : forall y : P, op' id' y = y)
    (op_id_r' : forall x : P, op' x id' = x)
    (op_assoc' : forall x y z : P, op' (op' x y) z = op' x (op' y z))
    (x y z : FM A),
      ap (FM_rec i' op' id' op_id_l' op_id_r' op_assoc') (op_assoc x y z)
        =
      op_assoc'
        (FM_rec i' op' id' op_id_l' op_id_r' op_assoc' x)
        (FM_rec i' op' id' op_id_l' op_id_r' op_assoc' y)
        (FM_rec i' op' id' op_id_l' op_id_r' op_assoc' z).

Fixpoint FM_ind
  {A : Type} {P : FM A -> Type}
  (i'        : forall a : A, P (i a))
  (op'       : forall {x y : FM A}, P x -> P y -> P (op x y))
  (id'       : P id)
  (op_id_l'  : forall {y : FM A} (py : P y), transport _ (op_id_l y) (op' id' py) = py)
  (op_id_r'  : forall {x : FM A} (px : P x), transport _ (op_id_r x) (op' px id') = px)
  (op_assoc' : forall {x y z : FM A} (px : P x) (py : P y) (pz : P z),
                 transport _ (op_assoc x y z) (op' (op' px py) pz) = op' px (op' py pz))
  (x : FM A) : P x :=
match x with
    | i a    => i' a
    | op a b => op' (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc') a)
                    (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc') b)
    | id    => id'
end.

Axiom FM_ind_op_id_l :
  forall
    {A : Type} {P : FM A -> Type}
    (i'        : forall a : A, P (i a))
    (op'       : forall {x y : FM A}, P x -> P y -> P (op x y))
    (id'       : P id)
    (op_id_l'  : forall {y : FM A} (py : P y), transport _ (op_id_l y) (op' id' py) = py)
    (op_id_r'  : forall {x : FM A} (px : P x), transport _ (op_id_r x) (op' px id') = px)
    (op_assoc' : forall {x y z : FM A} (px : P x) (py : P y) (pz : P z),
                   transport _ (op_assoc x y z) (op' (op' px py) pz) = op' px (op' py pz))
    (y : FM A),
      apd (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc')) (op_id_l y)
        =
      op_id_l' (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc') y).

Axiom FM_ind_op_id_r :
  forall
    {A : Type} {P : FM A -> Type}
    (i'        : forall a : A, P (i a))
    (op'       : forall {x y : FM A}, P x -> P y -> P (op x y))
    (id'       : P id)
    (op_id_l'  : forall {y : FM A} (py : P y), transport _ (op_id_l y) (op' id' py) = py)
    (op_id_r'  : forall {x : FM A} (px : P x), transport _ (op_id_r x) (op' px id') = px)
    (op_assoc' : forall {x y z : FM A} (px : P x) (py : P y) (pz : P z),
                   transport _ (op_assoc x y z) (op' (op' px py) pz) = op' px (op' py pz))
    (x : FM A),
      apd (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc')) (op_id_r x)
        =
      op_id_r' (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc') x).

Axiom FM_ind_op_assoc :
  forall
    {A : Type} {P : FM A -> Type}
    (i'        : forall a : A, P (i a))
    (op'       : forall {x y : FM A}, P x -> P y -> P (op x y))
    (id'       : P id)
    (op_id_l'  : forall {y : FM A} (py : P y), transport _ (op_id_l y) (op' id' py) = py)
    (op_id_r'  : forall {x : FM A} (px : P x), transport _ (op_id_r x) (op' px id') = px)
    (op_assoc' : forall {x y z : FM A} (px : P x) (py : P y) (pz : P z),
                   transport _ (op_assoc x y z) (op' (op' px py) pz) = op' px (op' py pz))
    (x y z : FM A),
      apd (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc')) (op_assoc x y z)
        =
      op_assoc'
        (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc') x)
        (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc') y)
        (FM_ind i' (@op') id' (@op_id_l') (@op_id_r') (@op_assoc') z).

End FreeMon.

Import FreeMon.

Lemma f :
  forall {A : Type} (x : FM A), list A.
Proof.
  intros A x.
  refine (FM_rec
          (fun a => [a])
          (fun l1 l2 => app l1 l2)
          []
          _ _ _ x).
    cbn. refl.
    induction x0; cbn.
      refl.
      apply ap. assumption.
    induction x0; cbn.
      refl.
      intros. apply ap. apply IHx0.
Defined.

Fixpoint g {A : Type} (l : list A) : FM A :=
match l with
    | nil => id
    | cons h t => op (i h) (g t)
end.

Lemma g_app :
  forall {A : Type} (l1 l2 : list A),
    g (app l1 l2) = op (g l1) (g l2).
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    apply inv. apply op_id_l.
    rewrite op_assoc. apply ap. apply IHt1.
Defined.

Definition ap2 {A B C : Type} (f : A -> B -> C) {a a' : A} {b b' : B} (p : a = a') (q : b = b') : f a b = f a' b' :=
match p, q with
    | refl _, refl _ => refl _
end.

Lemma fg :
  forall {A : Type} (x : FM A),
    g (f x) = x.
Proof.
  intro.
  refine (FM_ind _ _ _ _ _ _).
  Unshelve. 2-6: cycle 3.
    cbn. intros. apply op_id_r.
    intros. change (f (op x y)) with (app (f x) (f y)).
      exact (cat (g_app (f x) (f y)) (ap2 op X X0)).
    cbn. refl.
    2: { intros. rewrite transport_eq_fun_dep. admit. }
    admit.
    admit.
Admitted.

Lemma gf :
  forall {A : Type} (l : list A),
    f (g l) = l.
Proof.
  induction l as [| h t].
    refl.
    change (app (f (i h)) (f (g t)) = cons h t).
Abort.