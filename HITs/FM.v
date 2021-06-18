Require Export HoTT.

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

Require Import List.
Import ListNotations.

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
    admit.
    admit.
Admitted.