Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

(* Record fiber {A B : U} (f : A -> B) (b : B) : U :=
{
    domp : A;
    domp_spec : f domp = b;
}.

Arguments domp {A B f b} _.
 *)

Definition fiber {A B : U} (f : A -> B) (b : B) : U :=
  {a : A & f a = b}.

Class Codomain (B : U) (P : U -> U) : U :=
{
    E : U;
    pr : E -> B;
    spec : forall b : B, fiber (comp pr b);
}.

#[refine]
Instance wut {B : Type} (P : Type -> Type) (f : B -> {A : Type & P A}) : Codomain B P :=
{|
(*     E := {b : B & P (pr1' (f b))}; *)
    E := {x : {A : Type  & P A} & fiber f x};
|}.
Proof.
  intro x. exact (pr1' (pr2' x)).
  intro. unfold fiber. Check (pr1' (pr2' (f b))). compute. cbn.
  pose (f b).
  cbn in s.

 compute in *. Check (pr2' (f b)).
  intro. assert ( exact (pr2' (f b)). cbn.
  intro b.
  destruct (f b).
  compute. apply p.

Definition tuw {B : U} (P : U -> U) (x : Codomain B P) : B -> {A : U & P A}.
Proof.
  destruct x.
  intro b.
  exists (fiber pr0 b). apply spec0.
Defined.

Record Iso (A B : U) : U :=
{
    coe   : A -> B;
    uncoe : B -> A;
    coe_uncoe : forall a : A, uncoe (coe a) = a;
    uncoe_coe : forall b : B, coe (uncoe b) = b;
}.

Axiom funext : forall {A B : U} (f g : A -> B), (forall x : A, f x = g x) -> f = g.

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