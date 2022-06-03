From HoTT Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

Module Circle.

Private Inductive Circle : Type :=
    | base : Circle.

Axiom loop : base = base.

Definition Circle_rec
  {P : Type} (b : P) (l : b = b) : Circle -> P :=
    fun c : Circle => b.

Axiom Circle_rec_loop :
  forall {P : Type} (b : P) (l : b = b),
    ap (Circle_rec b l) loop = l.

Definition Circle_ind
  {P : Circle -> Type}
  (b : P base) (l : transport _ loop b = b)
  (c : Circle) : P c :=
match c with
    | base => b
end.

Axiom Circle_ind_loop :
  forall {P : Circle -> Type} (b : P base) (l : transport _ loop b = b) (c : Circle),
    apd (Circle_ind b l) loop = l.

End Circle.

Module WeirdCircle.

Private Inductive WeirdCircle : Type :=
    | N : WeirdCircle
    | S : WeirdCircle.

Axiom NS : N = S.
Axiom SN : S = N.

Definition WeirdCircle_rec
  {P : Type} (n s : P) (ns : n = s) (sn : s = n) (c : WeirdCircle) : P :=
match c with
    | N => n
    | S => s
end.

Axiom WeirdCircle_rec_NS :
  forall {P : Type} (n s : P) (ns : n = s) (sn : s = n) (c : WeirdCircle),
    ap (WeirdCircle_rec n s ns sn) NS = ns.

Axiom WeirdCircle_rec_SN :
  forall {P : Type} (n s : P) (ns : n = s) (sn : s = n) (c : WeirdCircle),
    ap (WeirdCircle_rec n s ns sn) SN = sn.

Definition WeirdCircle_ind
  {P : WeirdCircle -> Type}
  (n : P N) (s : P S)
  (ns : transport _ NS n = s) (sn : transport _ SN s = n)
  (c : WeirdCircle) : P c :=
match c with
    | N => n
    | S => s
end.

Axiom WeirdCircle_ind_NS :
  forall
    {P : WeirdCircle -> Type} (n : P N) (s : P S)
    (ns : transport _ NS n = s) (sn : transport _ SN s = n)
    (c : WeirdCircle),
      apd (WeirdCircle_ind n s ns sn) NS = ns.

Axiom WeirdCircle_ind_SN :
  forall
    {P : WeirdCircle -> Type} (n : P N) (s : P S)
    (ns : transport _ NS n = s) (sn : transport _ SN s = n)
    (c : WeirdCircle),
      apd (WeirdCircle_ind n s ns sn) SN = sn.

End WeirdCircle.

Import Circle WeirdCircle.

Definition cw (c : Circle) : WeirdCircle :=
  Circle_rec N (cat NS SN) c.

Definition wc (w : WeirdCircle) : Circle :=
  WeirdCircle_rec base base loop loop w.

Lemma cw_wc :
  forall c : Circle,
    wc (cw c) = c.
Proof.
  eapply Circle_ind. Unshelve.
  all: cycle 1; cbn.
    exact loop.
Abort.

Lemma wc_cw :
  forall c : WeirdCircle,
    cw (wc c) = c.
Proof.
  eapply WeirdCircle_ind. Unshelve. all: cycle 2; cbn.
    compute. reflexivity.
    compute. exact NS.
Abort.