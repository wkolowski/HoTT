From HoTT Require Export HoTT.

Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

Definition UPair (A : U) : U :=
  {X : U & trunc (equiv X bool) * (X -> A)}.

Definition upair {A : U} (x y : A) : UPair A.
Proof.
  split with {a : A & (a = x) + (a = y)}.
  split.
  - apply trunc'. esplit. Unshelve. all: cycle 1.
    + intros [a [H | H]].
      * exact true.
      * exact false.
    + apply qinv_isequiv.
      cbn; red. esplit. Unshelve. all: cycle 1.
      * intros [].
        -- exists x. left. reflexivity.
        -- exists y. right. reflexivity.
      * split.
        -- red. intros []; cbn; reflexivity.
        -- red. intros [a [[] | []]]; cbn; reflexivity.
  - exact pr1'.
Defined.

Lemma uswap :
  forall {A : U} (x y : A),
    upair x y = upair y x.
Proof.
  intros A x y.
  unfold upair.
  apply sigma_eq_intro. cbn. esplit. Unshelve. all: cycle 1.
  - apply ua. esplit. Unshelve. all: cycle 1.
    + intros [a []]; exists a.
      * right; assumption.
      * left; assumption.
    + cbn. apply qinv_isequiv. red. esplit. Unshelve. all: cycle 1.
      * intros [a []]; exists a.
        -- right; assumption.
        -- left; assumption.
      * split; compute.
        -- intros [a []]; reflexivity.
        -- intros [a []]; reflexivity.
  - apply prod_eq_intro. split.
    + cbn. apply path.
    + cbn. apply funext. intros [a [[] | []]]. cbn.
      * destruct (transport _). cbn. admit.
      * admit.
Admitted.

(* Lemma upair_easy :
  forall {A : U} (x1 x2 y1 y2 : A),
    (upair x1 y1 = upair x2 y2) = 

Lemma upair_char :
  forall {A : U} (x1 x2 y1 y2 : A),
    (upair x1 y1 = upair x2 y2) =  *)