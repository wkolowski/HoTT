From HoTT Require Export HoTT.
From HoTT.Univs Require Export DProp.

Definition dni {A : U} : A -> ~ ~ A :=
  fun a na => na a.

Definition Stable (A : U) : U :=
  ~ ~ A -> A.

Definition Stable_empty : Stable empty :=
  fun nne => nne id.

Definition Stable_unit : Stable unit :=
  fun _ => tt.

Definition Stable_inhabited (A : U) (x : A) : Stable A :=
  fun _ => x.

Definition Stable_not (A : U) : Stable (~ A) :=
  fun nnna a => nnna (fun nna => nna a).

Definition Stable_prod (A B : U) (sa : Stable A) (sb : Stable B) : Stable (A * B) :=
  fun nnab =>
    (sa (fun na => nnab (fun '(a, _) => na a)),
     sb (fun nb => nnab (fun '(_, b) => nb b))).

Definition Stable_pi
  (A : U) (B : A -> U) (sb : forall a : A, Stable (B a)) : Stable (forall a : A, B a) :=
    fun nnb a => sb a (fun nb => nnb (fun f => nb (f a))).

Definition Stable_fun (A B : U) (sb : Stable B) : Stable (A -> B) :=
  Stable_pi A (fun _ => B) (fun _ => sb).

Lemma isProp_Stable :
  forall A : U,
    isProp A -> isProp (Stable A).
Proof.
  unfold Stable, isProp.
  intros A h f g.
  apply funext; intros x.
  apply h.
Defined.

Lemma isProp_Stable_inv :
  forall A : U,
    isProp (Stable A) -> isProp A.
Proof.
  unfold Stable, isProp.
  intros A h x y.
  specialize (h (fun _ => x) (fun _ => y)).
  apply (ap (fun f => f (dni x))) in h.
  cbn in h.
  assumption.
Defined.

Definition isStProp (A : U) : U :=
  isProp A * Stable A.

Lemma isProp_isStProp :
  forall A : U,
    isProp (isStProp A).
Proof.
  intros A.
  unfold isStProp.
  apply isProp_prod'.
  - apply isProp_Stable.
  - intros _.
    apply isProp_isProp.
Defined.

Lemma isStProp_char1 :
  forall A : U,
    isStProp A <-> isContr (Stable A).
Proof.
  intros A.
  unfold isStProp.
  rewrite isContr_isProp_inhabited.
  split.
  - intros []; split; [assumption |].
    apply isProp_Stable; assumption.
  - intros []; split; [| assumption].
    apply isProp_Stable_inv; assumption.
Defined.

Lemma isStProp_char2 :
  forall A : U,
    isStProp A <-> (~ ~ A -> isContr A).
Proof.
  intros A.
  unfold isStProp.
  rewrite isContr_isProp_inhabited.
  split.
  - intros [h s] nna; split; [| assumption].
    apply s, nna.
  - intros f.
    assert (s : Stable A).
    {
      intros nna.
      apply f.
      assumption.
    }
    split; [| assumption].
    intros x; assert (a := x); revert x.
    apply f; intros na.
    apply na, a.
Defined.

Lemma isStProp_char3 :
  forall A : U,
    isStProp A <-> isequiv (@dni A).
Proof.
  split.
  - intros [h s].
    apply qinv_isequiv.
    exists s.
    split; compute.
    + intros nna.
      apply isProp_fun, isProp_empty.
    + intros a.
      apply h.
  - intros [_ [dne h]]; compute in h.
    unfold isStProp.
    split; [| assumption].
    intros x y.
    rewrite <- (h x), <- (h y).
    apply ap.
    apply isProp_fun, isProp_empty.
Defined.

Lemma isStProp_empty : isStProp empty.
Proof.
  split.
  - apply isProp_empty.
  - apply Stable_empty.
Defined.

Lemma isStProp_unit : isStProp unit.
Proof.
  split.
  - apply isProp_unit.
  - apply Stable_unit.
Defined.

Lemma isStProp_not :
  forall A : U,
    isStProp (~ A).
Proof.
  split.
  - apply isProp_fun, isProp_empty.
  - apply Stable_not.
Defined.

Lemma isStProp_prod :
  forall A B : U,
    isStProp A -> isStProp B -> isStProp (A * B).
Proof.
  intros A B [ha sa] [hb sb]; split.
  - apply isProp_prod; assumption.
  - apply Stable_prod; assumption.
Defined.

Lemma isStProp_pi :
  forall (A : U) (B : A -> U),
    (forall a : A, isStProp (B a)) -> isStProp (forall a : A, B a).
Proof.
  intros A B sb; split.
  - apply isProp_pi; intros x; apply sb.
  - apply Stable_pi; intros x; apply sb.
Defined.

Lemma isStProp_fun (A B : U) (sb : isStProp B) : isStProp (A -> B).
Proof.
  apply isStProp_pi; intros _; assumption.
Defined.
