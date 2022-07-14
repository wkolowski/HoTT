From HoTT Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

Module Interval.

Private Inductive I : Type :=
| i0 : I
| i1 : I.

Axiom seg : i0 = i1.

Definition I_rec {P : Type} (p0 p1 : P) (p : p0 = p1) (i : I) : P :=
match i with
| i0 => p0
| i1 => p1
end.

Axiom I_rec_seg :
  forall {P : Type} (p0 p1 : P) (p : p0 = p1),
    ap (I_rec p0 p1 p) seg = p.

Definition I_ind
  {P : I -> Type} (p0 : P i0) (p1 : P i1) (p : transport _ seg p0 = p1) (i : I) : P i :=
match i with
| i0 => p0
| i1 => p1
end.

Axiom I_ind_seg :
  forall {P : I -> Type} (p0 : P i0) (p1 : P i1) (p : transport _ seg p0 = p1) (i : I),
    apd (I_ind p0 p1 p) seg = p.

End Interval.
