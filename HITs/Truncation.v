From HoTT Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

Module Tr.

Private Inductive Tr (A : Type) : Type :=
| tr : A -> Tr A.

Axiom isProp_Tr : forall {A : Type} (x y : Tr A), x = y.

Arguments tr {A} _.

Definition Tr_rec {A B : Type} (f : A -> B) (p : forall x y : A, f x = f y) (t : Tr A) :=
match t with
| tr a => f a
end.

Axiom Tr_rec_comp :
  forall {A B : Type} (f : A -> B) (p : forall x y : A, f x = f y) (x y : A),
    ap (Tr_rec f p) (isProp_Tr (tr x) (tr y)) = p x y.

Definition Tr_ind
  {A : Type} {B : Tr A -> Type}
  (f : forall a : A, B (tr a))
  (p : forall x y : A, transport _ (isProp_Tr (tr x) (tr y)) (f x) = f y)
  (t : Tr A) : B t :=
match t with
| tr a => f a
end.

Axiom Tr_ind_comp :
  forall
    {A : Type} {B : Tr A -> Type}
    (f : forall a : A, B (tr a))
    (p : forall x y : A, transport _ (isProp_Tr (tr x) (tr y)) (f x) = f y)
    (x y : A),
      apd (Tr_ind f p) (isProp_Tr (tr x) (tr y)) = p x y.

End Tr.