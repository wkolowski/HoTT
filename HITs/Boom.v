Require Import StrictProp.

From HoTT Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

Inductive Law : Type :=
    | Id
    | Assoc
    | Comm
    | Idem.

Definition Laws : Type := Law -> bool.

(*
Definition Magma (f : Law -> bool) : bool := true.

Definition Semigroup (f : Law -> bool) : bool :=
  f Assoc.

Definition Monoid (f : Law -> bool) : bool :=
  f Assoc && f Id.

Definition CommutativeMonoid (f : Law -> bool) : bool :=
  Monoid f && f Comm.
*)

Module Boom.

Private Inductive Boom (A : Type) (f : Law -> bool) : Type :=
    | i  : A -> Boom A f
    | op : Boom A f -> Boom A f -> Boom A f
    | id : Squash (f Id = true) -> Boom A f.

Arguments i  {A f} _.
Arguments op {A f} _ _.
Arguments id {A f} _.

Axiom idl :
  forall
    {A : Type} {f : Law -> bool}
    (s : Squash (f Id = true)) (y : Boom A f),
      op (id s) y = y.
Axiom idr :
  forall
    {A : Type} {f : Law -> bool}
    (s : Squash (f Id = true)) (x : Boom A f),
      op x (id s) = x.
Axiom assoc :
  forall
    {A : Type} {f : Law -> bool}
    (s : Squash (f Assoc = true)) (x y z : Boom A f),
      op (op x y) z = op x (op y z).
Axiom comm :
  forall
    {A : Type} {f : Law -> bool}
    (s : Squash (f Comm = true)) (x y : Boom A f),
      op x y = op y x.
Axiom idem :
  forall
    {A : Type} {f : Law -> bool}
    (s : Squash (f Idem = true)) (x : Boom A f),
      op x x = x.

Fixpoint Boom_rec
  {A : Type} {f : Law -> bool}
  {P : Type}
  (i'     : A -> P)
  (op'    : P -> P -> P)
  (id'    : Squash (f Id    = true) -> P)
  (idl'   : forall (s : Squash (f Id    = true)) (y     : P), op' (id' s) y = y)
  (idr'   : forall (s : Squash (f Id    = true)) (x     : P), op' x (id' s) = x)
  (assoc' : forall (s : Squash (f Assoc = true)) (x y z : P), op' (op' x y) z = op' x (op' y z))
  (comm'  : forall (s : Squash (f Comm  = true)) (x y   : P), op' x y = op' y x)
  (idem'  : forall (s : Squash (f Idem  = true)) (x     : P), op' x x = x)
  (x : Boom A f) : P :=
match x with
    | i a => i' a
    | op a b => op' (Boom_rec i' op' id' idl' idr' assoc' comm' idem' a)
                    (Boom_rec i' op' id' idl' idr' assoc' comm' idem' b)
    | id s => id' s
end.

Axiom Boom_rec_idl :
  forall
    {A : Type} {f : Law -> bool}
    {P : Type}
    (i'     : A -> P)
    (op'    : P -> P -> P)
    (id'    : Squash (f Id    = true) -> P)
    (idl'   : forall (s : Squash (f Id    = true)) (y     : P), op' (id' s) y = y)
    (idr'   : forall (s : Squash (f Id    = true)) (x     : P), op' x (id' s) = x)
    (assoc' : forall (s : Squash (f Assoc = true)) (x y z : P), op' (op' x y) z = op' x (op' y z))
    (comm'  : forall (s : Squash (f Comm  = true)) (x y   : P), op' x y = op' y x)
    (idem'  : forall (s : Squash (f Idem  = true)) (x     : P), op' x x = x)
    (s : Squash (f Id = true)) (y : Boom A f),
      ap (Boom_rec i' op' id' idl' idr' assoc' comm' idem') (idl s y)
        =
      idl' s (Boom_rec i' op' id' idl' idr' assoc' comm' idem' y).

Axiom Boom_rec_idr :
  forall
    {A : Type} {f : Law -> bool}
    {P : Type}
    (i'     : A -> P)
    (op'    : P -> P -> P)
    (id'    : Squash (f Id    = true) -> P)
    (idl'   : forall (s : Squash (f Id    = true)) (y     : P), op' (id' s) y = y)
    (idr'   : forall (s : Squash (f Id    = true)) (x     : P), op' x (id' s) = x)
    (assoc' : forall (s : Squash (f Assoc = true)) (x y z : P), op' (op' x y) z = op' x (op' y z))
    (comm'  : forall (s : Squash (f Comm  = true)) (x y   : P), op' x y = op' y x)
    (idem'  : forall (s : Squash (f Idem  = true)) (x     : P), op' x x = x)
    (s : Squash (f Id = true)) (x : Boom A f),
      ap (Boom_rec i' op' id' idl' idr' assoc' comm' idem') (idr s x)
        =
      idr' s (Boom_rec i' op' id' idl' idr' assoc' comm' idem' x).

Axiom Boom_rec_assoc :
  forall
    {A : Type} {f : Law -> bool}
    {P : Type}
    (i'     : A -> P)
    (op'    : P -> P -> P)
    (id'    : Squash (f Id    = true) -> P)
    (idl'   : forall (s : Squash (f Id    = true)) (y     : P), op' (id' s) y = y)
    (idr'   : forall (s : Squash (f Id    = true)) (x     : P), op' x (id' s) = x)
    (assoc' : forall (s : Squash (f Assoc = true)) (x y z : P), op' (op' x y) z = op' x (op' y z))
    (comm'  : forall (s : Squash (f Comm  = true)) (x y   : P), op' x y = op' y x)
    (idem'  : forall (s : Squash (f Idem  = true)) (x     : P), op' x x = x)
    (s : Squash (f Assoc = true)) (x y z : Boom A f),
      ap (Boom_rec i' op' id' idl' idr' assoc' comm' idem') (assoc s x y z)
        =
      assoc' s
        (Boom_rec i' op' id' idl' idr' assoc' comm' idem' x)
        (Boom_rec i' op' id' idl' idr' assoc' comm' idem' y)
        (Boom_rec i' op' id' idl' idr' assoc' comm' idem' z).

Axiom Boom_rec_comm :
  forall
    {A : Type} {f : Law -> bool}
    {P : Type}
    (i'     : A -> P)
    (op'    : P -> P -> P)
    (id'    : Squash (f Id    = true) -> P)
    (idl'   : forall (s : Squash (f Id    = true)) (y     : P), op' (id' s) y = y)
    (idr'   : forall (s : Squash (f Id    = true)) (x     : P), op' x (id' s) = x)
    (assoc' : forall (s : Squash (f Assoc = true)) (x y z : P), op' (op' x y) z = op' x (op' y z))
    (comm'  : forall (s : Squash (f Comm  = true)) (x y   : P), op' x y = op' y x)
    (idem'  : forall (s : Squash (f Idem  = true)) (x     : P), op' x x = x)
    (s : Squash (f Comm = true)) (x y : Boom A f),
      ap (Boom_rec i' op' id' idl' idr' assoc' comm' idem') (comm s x y)
        =
      comm' s
        (Boom_rec i' op' id' idl' idr' assoc' comm' idem' x)
        (Boom_rec i' op' id' idl' idr' assoc' comm' idem' y).

Axiom Boom_rec_idem :
  forall
    {A : Type} {f : Law -> bool}
    {P : Type}
    (i'     : A -> P)
    (op'    : P -> P -> P)
    (id'    : Squash (f Id    = true) -> P)
    (idl'   : forall (s : Squash (f Id    = true)) (y     : P), op' (id' s) y = y)
    (idr'   : forall (s : Squash (f Id    = true)) (x     : P), op' x (id' s) = x)
    (assoc' : forall (s : Squash (f Assoc = true)) (x y z : P), op' (op' x y) z = op' x (op' y z))
    (comm'  : forall (s : Squash (f Comm  = true)) (x y   : P), op' x y = op' y x)
    (idem'  : forall (s : Squash (f Idem  = true)) (x     : P), op' x x = x)
    (s : Squash (f Idem = true)) (x : Boom A f),
      ap (Boom_rec i' op' id' idl' idr' assoc' comm' idem') (idem s x)
        =
      idem' s
        (Boom_rec i' op' id' idl' idr' assoc' comm' idem' x).

Fixpoint Boom_ind
  {A : Type} {f : Law -> bool}
  {P : Boom A f -> Type}
  (i'     : forall a : A, P (i a))
  (op'    : forall {x y : Boom A f}, P x -> P y -> P (op x y))
  (id'    : forall (s : Squash (f Id = true)), P (id s))
  (idl'   : forall (s : Squash (f Id = true)) {y : Boom A f} (py : P y),
              transport _ (idl s y) (op' (id' s) py) = py)
  (idr'   : forall (s : Squash (f Id = true)) {x : Boom A f} (px : P x),
              transport _ (idr s x) (op' px (id' s)) = px)
  (assoc' : forall (s : Squash (f Assoc = true)) {x y z : Boom A f} (px : P x) (py : P y) (pz : P z),
              transport _ (assoc s x y z) (op' (op' px py) pz) = op' px (op' py pz))
  (comm'  : forall (s : Squash (f Comm = true)) {x y : Boom A f} (px : P x) (py : P y),
              transport _ (comm s x y) (op' px py) = op' py px)
  (idem'  : forall (s : Squash (f Idem = true)) {x : Boom A f} (px : P x),
              transport _ (idem s x) (op' px px) = px)
  (x : Boom A f) : P x :=
match x with
    | i a    => i' a
    | op a b => op' (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' a)
                    (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' b)
    | id s   => id' s
end.

Axiom Boom_ind_idl :
  forall
    {A : Type} {f : Law -> bool}
    {P : Boom A f -> Type}
    (i'     : forall a : A, P (i a))
    (op'    : forall {x y : Boom A f}, P x -> P y -> P (op x y))
    (id'    : forall (s : Squash (f Id = true)), P (id s))
    (idl'   : forall (s : Squash (f Id = true)) {y : Boom A f} (py : P y),
                transport _ (idl s y) (op' (id' s) py) = py)
    (idr'   : forall (s : Squash (f Id = true)) {x : Boom A f} (px : P x),
                transport _ (idr s x) (op' px (id' s)) = px)
    (assoc' : forall (s : Squash (f Assoc = true)) {x y z : Boom A f} (px : P x) (py : P y) (pz : P z),
                transport _ (assoc s x y z) (op' (op' px py) pz) = op' px (op' py pz))
    (comm'  : forall (s : Squash (f Comm = true)) {x y : Boom A f} (px : P x) (py : P y),
                transport _ (comm s x y) (op' px py) = op' py px)
    (idem'  : forall (s : Squash (f Idem = true)) {x : Boom A f} (px : P x),
                transport _ (idem s x) (op' px px) = px)
    (s : Squash (f Id = true)) (y : Boom A f),
      apd (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem') (idl s y)
        =
      idl' s (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' y).

Axiom Boom_ind_idr :
  forall
    {A : Type} {f : Law -> bool}
    {P : Boom A f -> Type}
    (i'     : forall a : A, P (i a))
    (op'    : forall {x y : Boom A f}, P x -> P y -> P (op x y))
    (id'    : forall (s : Squash (f Id = true)), P (id s))
    (idl'   : forall (s : Squash (f Id = true)) {y : Boom A f} (py : P y),
                transport _ (idl s y) (op' (id' s) py) = py)
    (idr'   : forall (s : Squash (f Id = true)) {x : Boom A f} (px : P x),
                transport _ (idr s x) (op' px (id' s)) = px)
    (assoc' : forall (s : Squash (f Assoc = true)) {x y z : Boom A f} (px : P x) (py : P y) (pz : P z),
                transport _ (assoc s x y z) (op' (op' px py) pz) = op' px (op' py pz))
    (comm'  : forall (s : Squash (f Comm = true)) {x y : Boom A f} (px : P x) (py : P y),
                transport _ (comm s x y) (op' px py) = op' py px)
    (idem'  : forall (s : Squash (f Idem = true)) {x : Boom A f} (px : P x),
                transport _ (idem s x) (op' px px) = px)
    (s : Squash (f Id = true)) (x : Boom A f),
      apd (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem') (idr s x)
        =
      idr' s (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' x).

Axiom Boom_ind_assoc :
  forall
    {A : Type} {f : Law -> bool}
    {P : Boom A f -> Type}
    (i'     : forall a : A, P (i a))
    (op'    : forall {x y : Boom A f}, P x -> P y -> P (op x y))
    (id'    : forall (s : Squash (f Id = true)), P (id s))
    (idl'   : forall (s : Squash (f Id = true)) {y : Boom A f} (py : P y),
                transport _ (idl s y) (op' (id' s) py) = py)
    (idr'   : forall (s : Squash (f Id = true)) {x : Boom A f} (px : P x),
                transport _ (idr s x) (op' px (id' s)) = px)
    (assoc' : forall (s : Squash (f Assoc = true)) {x y z : Boom A f} (px : P x) (py : P y) (pz : P z),
                transport _ (assoc s x y z) (op' (op' px py) pz) = op' px (op' py pz))
    (comm'  : forall (s : Squash (f Comm = true)) {x y : Boom A f} (px : P x) (py : P y),
                transport _ (comm s x y) (op' px py) = op' py px)
    (idem'  : forall (s : Squash (f Idem = true)) {x : Boom A f} (px : P x),
                transport _ (idem s x) (op' px px) = px)
    (s : Squash (f Assoc = true)) (x y z : Boom A f),
      apd (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem') (assoc s x y z)
        =
      assoc' s
        (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' x)
        (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' y)
        (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' z).

Axiom Boom_ind_comm :
  forall
    {A : Type} {f : Law -> bool}
    {P : Boom A f -> Type}
    (i'     : forall a : A, P (i a))
    (op'    : forall {x y : Boom A f}, P x -> P y -> P (op x y))
    (id'    : forall (s : Squash (f Id = true)), P (id s))
    (idl'   : forall (s : Squash (f Id = true)) {y : Boom A f} (py : P y),
                transport _ (idl s y) (op' (id' s) py) = py)
    (idr'   : forall (s : Squash (f Id = true)) {x : Boom A f} (px : P x),
                transport _ (idr s x) (op' px (id' s)) = px)
    (assoc' : forall (s : Squash (f Assoc = true)) {x y z : Boom A f} (px : P x) (py : P y) (pz : P z),
                transport _ (assoc s x y z) (op' (op' px py) pz) = op' px (op' py pz))
    (comm'  : forall (s : Squash (f Comm = true)) {x y : Boom A f} (px : P x) (py : P y),
                transport _ (comm s x y) (op' px py) = op' py px)
    (idem'  : forall (s : Squash (f Idem = true)) {x : Boom A f} (px : P x),
                transport _ (idem s x) (op' px px) = px)
    (s : Squash (f Comm = true)) (x y : Boom A f),
      apd (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem') (comm s x y)
        =
      comm' s
        (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' x)
        (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' y).

Axiom Boom_ind_idem :
  forall
    {A : Type} {f : Law -> bool}
    {P : Boom A f -> Type}
    (i'     : forall a : A, P (i a))
    (op'    : forall {x y : Boom A f}, P x -> P y -> P (op x y))
    (id'    : forall (s : Squash (f Id = true)), P (id s))
    (idl'   : forall (s : Squash (f Id = true)) {y : Boom A f} (py : P y),
                transport _ (idl s y) (op' (id' s) py) = py)
    (idr'   : forall (s : Squash (f Id = true)) {x : Boom A f} (px : P x),
                transport _ (idr s x) (op' px (id' s)) = px)
    (assoc' : forall (s : Squash (f Assoc = true)) {x y z : Boom A f} (px : P x) (py : P y) (pz : P z),
                transport _ (assoc s x y z) (op' (op' px py) pz) = op' px (op' py pz))
    (comm'  : forall (s : Squash (f Comm = true)) {x y : Boom A f} (px : P x) (py : P y),
                transport _ (comm s x y) (op' px py) = op' py px)
    (idem'  : forall (s : Squash (f Idem = true)) {x : Boom A f} (px : P x),
                transport _ (idem s x) (op' px px) = px)
    (s : Squash (f Idem = true)) (x : Boom A f),
      apd (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem') (idem s x)
        =
      idem' s
        (Boom_ind i' (@op') id' idl' idr' assoc' comm' idem' x).

End Boom.