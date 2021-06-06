Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

Record fiber {A B : U} (f : A -> B) (b : B) : U :=
{
    aa : A;
    f_aa : f aa = b;
}.

Class Codomain (B : U) : U :=
{
    CE : U;
    Cf : CE -> B;
}.

#[refine]
Instance f {B : U} (P : B -> U) : Codomain B :=
{|
    CE := {b : B & P b};
|}.
Proof.
  destruct 1 as [b _]. exact b.
Defined.

Definition g {B : U} (x : Codomain B) : B -> U.
Proof.
  destruct x.
  intro b.
  exact (fiber Cf0 b).
Defined.

Record Iso (A B : U) : U :=
{
    coe   : A -> B;
    uncoe : B -> A;
    coe_uncoe : forall a : A, uncoe (coe a) = a;
    uncoe_coe : forall b : B, coe (uncoe b) = b;
}.

Axiom funext : forall {A B : U} (f g : A -> B), (forall x : A, f x = g x) -> f = g.
(* Axiom ua     : forall {A B : U}, Iso A B -> A = B. *)

Lemma fg :
  forall {A : U} (P : A -> U),
    g (f P) = P.
Proof.
  intros.
  unfold f, g in *.
  apply funext.
  intro a.
  apply ua. esplit. apply qinv_isequiv. Unshelve. all: cycle 1.
    destruct 1. destruct aa0. exact (transport _ f_aa0 p).
    esplit. Unshelve. all: cycle 1.
      intro. esplit. Unshelve. all: cycle 2.
        split with a. assumption.
        cbn. reflexivity.
      split.
        compute. reflexivity.
        red. destruct x as [[] []]. compute. reflexivity.
Defined.

Lemma ua_Codomain :
  forall
    {B : U} (x y : Codomain B)
    (p : @CE _ x = @CE _ y) (q : transport (fun t => t -> B) p (@Cf _ x) = @Cf _ y), x = y.
Proof.
  destruct x, y. cbn.
  destruct p. cbn.
  destruct 1.
  reflexivity.
Defined.

Lemma gf :
  forall {B : U} (x : Codomain B),
    f (g x) = x.
Proof.
  intros.
  eapply ua_Codomain.
  Unshelve. all: cycle 1.
    cbn. destruct x. cbn. apply ua. esplit. apply qinv_isequiv. Unshelve. all: cycle 2.
      destruct 1 as [b []]. exact aa0.
      esplit. Unshelve. all: cycle 2.
        intro x. split with (Cf0 x). esplit. Unshelve. all: cycle 3.
          exact x.
          reflexivity.
        split.
          compute. reflexivity.
          red. destruct x as [b []]. compute. destruct f_aa0. reflexivity.
    destruct x. cbn. apply funext. intro.
    {
      rewrite transport_fun.
      rewrite transportconst.
      rewrite inv_ua.
      rewrite transport_ua.
      cbn. reflexivity.
    }
Defined.