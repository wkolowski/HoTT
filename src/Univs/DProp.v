From HoTT Require Export HoTT.

Definition Dec (A : U) : U :=
  A + ~ A.

Lemma isProp_Dec :
  forall A : U,
    isProp A -> isProp (Dec A).
Proof.
  apply ex_3_6.
Defined.

Lemma isProp_Dec_inv :
  forall A : U,
    isProp (Dec A) -> isProp A.
Proof.
  unfold isProp, Dec.
  intros A h x y.
  rewrite <- (inl_eq_char A (~ A)).
  apply h.
Defined.

Record isDProp (P : U) : U :=
{
  isProp_DProp : isProp P;
  decide : P + ~ P;
}.

Arguments isProp_DProp {_} _.
Arguments decide {_} _.

Lemma isProp_isDProp :
  forall A : U,
    isProp (isDProp A).
Proof.
Admitted.

Lemma isDProp_isContrDec :
  forall (A : U),
    isDProp A ~ isContr (Dec A).
Proof.
  intros A.
  apply isProp_iff_equiv.
  - apply isProp_isDProp.
  - apply isProp_isContr.
  - intros [h d].
    rewrite isContr_isProp_inhabited.
    split; [assumption |].
    apply isProp_Dec, h.
  - rewrite isContr_isProp_inhabited.
    intros [d h].
    split; [| assumption].
    apply isProp_Dec_inv, h.
Defined.

Definition iff (A B : U) : U :=
  (A -> B) * (B -> A).

Notation "A <-> B" := (iff A B) (at level 95, no associativity).

Lemma isProp_iff :
  forall A B : U,
    isProp A -> isProp B -> isProp (A <-> B).
Proof.
  intros A B hA hB.
  apply isProp_prod; apply isProp_fun; assumption.
Defined.

Lemma uninhabited_equiv_empty :
  forall A : U,
    ~ A -> A ~ empty.
Proof.
  intros A na.
  exists na.
  apply qinv_isequiv; red.
  exists empty_rec'.
  split; red.
  - destruct x.
  - intros a. contradiction.
Qed.

Lemma isDProp_boolean_decider :
  forall (A : U),
    isDProp A ~ { b : bool & A ~ if b then unit else empty }.
Proof.
  intros A.
  apply isProp_iff_equiv.
  - apply isProp_isDProp.
  - intros [x hx] [y hy].
    apply sigma_eq_intro; cbn.
    destruct x, y.
    + exists (refl true).
      assert (h : isProp (A ~ unit)).
      {
        admit.
      }
      apply h.
    + cut empty; [destruct 1 |].
      apply hy.
      destruct hx as [f [[g _] _]].
      apply g; exact tt.
    + cut empty; [destruct 1 |].
      apply hx.
      destruct hy as [f [[g _] _]].
      apply g; exact tt.
    + exists (refl false).
      admit.
  - intros [h d].
    destruct d as [a | na].
    + exists true.
      apply inhabited_isProp_unit; assumption.
    + exists false.
      apply uninhabited_equiv_empty; assumption.
Admitted.

Definition DProp : U :=
  {A : U & isDProp A}.

Section resizing.

Universe i j.

Constraint i < j.

(* Definition resize (D : DProp@{j}) : DProp@{i}. *)

End resizing.

Definition decideb (A : DProp) : bool :=
match decide (pr2' A) with
| inl _ => true
| inr _ => false
end.

Lemma isDProp_empty :
  isDProp empty.
Proof.
  split.
  - apply isProp_empty.
  - right; exact empty_rec'.
Defined.

Lemma isDProp_unit :
  isDProp unit.
Proof.
  split.
  - apply isProp_unit.
  - left; exact tt.
Defined.

Lemma isDProp_prod :
  forall A B : U,
    isDProp A -> isDProp B -> isDProp (A * B).
Proof.
  intros A B [hA dA] [hB dB].
  split.
  - apply isProp_prod; assumption.
  - destruct dA as [a | na].
    + destruct dB as [b | db].
      * left; exact (a, b).
      * right; intros [_ b]; contradiction.
    + right; intros [a _]; contradiction.
Defined.



Lemma equiv_DProp_bool :
  DProp ~ bool.
Proof.
  exists decideb.
  apply qinv_isequiv; red.
  exists (fun b : bool => if b then (| unit, isDProp_unit |) else (| empty, isDProp_empty |)).
  split.
  - intros []; cbn; refl.
  - intros [A [h [a | na]]]; unfold id; cbn.
    + apply sigma_eq_intro; cbn.
      admit.
    + apply sigma_eq_intro; cbn.
      admit.
Admitted.

Lemma Stable_isDProp :
  forall A : U,
    isDProp A -> ~ ~ A -> A.
Proof.
  intros A [h [a | na]] nna.
  - exact a.
  - apply empty_rec', nna, na.
Defined.


