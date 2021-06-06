Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

Module Suspension.

Private Inductive Susp (A : Type) : Type :=
    | N : Susp A
    | S : Susp A.

Arguments N {A}.
Arguments S {A}.

Axiom merid : forall {A : Type}, A -> @N A = @S A.

Definition Susp_rec {A B : Type} (n s : B) (m : forall x : A, n = s) (x : Susp A) : B :=
match x with
    | N => n
    | S => s
end.

Axiom Susp_rec_comp :
  forall {A B : Type} (N' S' : B) (m : A -> N' = S') (x : A),
    ap (Susp_rec N' S' m) (merid x) = m x.

End Suspension.