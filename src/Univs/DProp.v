From HoTT Require Export HoTT.

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

Definition Dec (A : U) : U :=
  A + ~ A.

Definition Dec_empty : Dec empty :=
  inr id.

Definition Dec_unit : Dec unit :=
  inl tt.

Definition Dec_inhabited (A : U) (x : A) : Dec A :=
  inl x.

Definition Dec_prod (A B : U) (da : Dec A) (db : Dec B) : Dec (A * B) :=
match da, db with
| inl a , inl b  => inl (a, b)
| inr na, _      => inr (fun '(a, _) => na a)
| _     , inr nb => inr (fun '(_, b) => nb b)
end.

Definition Dec_sum (A B : U) (da : Dec A) (db : Dec B) : Dec (A + B) :=
match da with
| inl a  => inl (inl a)
| inr na =>
  match db with
  | inl b  => inl (inr b)
  | inr nb => inr (fun ab =>
    match ab with
    | inl a => na a
    | inr b => nb b
    end)
  end
end.

Lemma Dec_fun :
  forall A B : U,
    Dec A -> Dec B -> Dec (A -> B).
Proof.
  intros A B dA dB.
  destruct dB as [b | nb].
  - exact (inl (fun _ => b)).
  - destruct dA as [a | na].
    + right; intros f. apply nb, f, a.
    + left.
      intros a.
      contradiction.
Defined.

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

Definition isDProp (P : U) : U := isProp P * Dec P.

Definition decide {A : U} (h : isDProp A) : A + ~ A := pr2 h.

Lemma isProp_prod' :
  forall A B : U,
    (A -> isProp B) -> (B -> isProp A) -> isProp (A * B).
Proof.
  intros A B hB hA.
  intros ab.
  assert (a : A) by (apply pr1 in ab; assumption).
  assert (b : B) by (apply pr2 in ab; assumption).
  revert ab.
  apply isProp_prod.
  - apply hA, b.
  - apply hB, a.
Defined.

Lemma isProp_isDProp :
  forall A : U,
    isProp (isDProp A).
Proof.
  intros A.
  apply isProp_prod'.
  - apply isProp_Dec.
  - intros _.
    apply isProp_isProp.
Defined.

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
Defined.

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
  - apply Dec_empty.
Defined.

Lemma isDProp_unit :
  isDProp unit.
Proof.
  split.
  - apply isProp_unit.
  - apply Dec_unit.
Defined.

Lemma isDProp_prod :
  forall A B : U,
    isDProp A -> isDProp B -> isDProp (A * B).
Proof.
  intros A B [hA dA] [hB dB].
  split.
  - apply isProp_prod; assumption.
  - apply Dec_prod; assumption.
Defined.

Lemma isDProp_fun :
  forall A B : U,
    isDProp A -> isDProp B -> isDProp (A -> B).
Proof.
  intros A B [hA dA] [hB dB]; split.
  - apply isProp_fun; assumption.
  - apply Dec_fun; assumption.
Defined.

Lemma isDProp_not:
  forall A : U,
    isDProp A -> isDProp (~ A).
Proof.
  intros A h.
  apply isDProp_fun; [assumption |].
  apply isDProp_empty.
Defined.

Lemma isDProp_semixor :
  forall A B : U,
    isDProp A -> isDProp B -> isDProp (A + (~ A) * B).
Proof.
  intros A B [hA dA] [hB dB]; split.
  - apply ex_3_7.
    + assumption.
    + apply isProp_prod; [| assumption].
      apply isProp_fun, isProp_empty.
    + intros [a [na b]]; contradiction.
  - destruct dA as [a | na].
    + exact (inl (inl a)).
    + destruct dB as [b | nb].
      * exact (inl (inr (na, b))).
      * apply inr; intros [a | [_ b]]; contradiction.
Defined.

Lemma equiv_DProp_bool :
  DProp ~ bool.
Proof.
  exists decideb.
  apply qinv_isequiv; red.
  exists (fun b : bool => if b then (| unit, isDProp_unit |) else (| empty, isDProp_empty |)).
  split; [intros []; cbn; refl |].
  intros [A [h [a | na]]]; unfold id; cbn.
  - apply sigma_eq_intro; cbn.
    unshelve esplit.
    + apply ua, equiv_sym.
      apply inhabited_isProp_unit; assumption.
    + apply prod_eq_intro; split.
      * apply isProp_isProp.
      * apply ex_3_6; assumption.
  - apply sigma_eq_intro; cbn.
    unshelve esplit.
    + apply ua, equiv_sym.
      apply uninhabited_equiv_empty; assumption.
    + apply prod_eq_intro; split.
      * apply isProp_isProp.
      * apply ex_3_6; assumption.
Defined.

Lemma Stable_isDProp :
  forall A : U,
    isDProp A -> ~ ~ A -> A.
Proof.
  intros A [h [a | na]] nna.
  - exact a.
  - apply empty_rec', nna, na.
Defined.
