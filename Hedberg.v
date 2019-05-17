Require Export HoTT.

Declare ML Module "ltac_plugin".
Local Set Default Proof Mode "Classic".

Set Universe Polymorphism.

(** This file is based on the paper "Generalizations of Hedberg's Theorem"
    by Kraus, Escardó, Coquand and Altenkirch. *)

(** TODO:
    1. bool -> nat is separated
    2. funext -> separated -> isSet
    3. isSet <-> || x = y || -> x = y
    4. ||X|| -> X <-> constant endomap
    5. fix f is prop
*)

(** * 2 Preliminaries *)

(* Definition 1 *)
Print decidable_equality.
(* ===> fun A : U => forall x y : A, (x = y) + (x <> y) : U -> U *)

Definition const {A B : U} (f : A -> B) : U :=
  forall x y : A, f x = f y.

Definition collapsible (A : U) : U :=
  {f : A -> A & const f}.

Definition path_collapsible (A : U) : U :=
  forall x y : A, collapsible (x = y).

(** * 3 Hedberg's Theorem *)

(* Lemma 1 *)
Lemma decidable_equality_path_collapsible :
  forall A : U,
    decidable_equality A -> path_collapsible A.
Proof.
  unfold decidable_equality, path_collapsible, collapsible.
  intros A DE x y. esplit.
Unshelve.
  Focus 2. intro p. destruct (DE x y) as [q | q].
    exact q.
    destruct (q p).
  unfold const. intros p q. destruct (DE x y).
    refl.
    destruct (n p).
Defined.

(* Lemma 2 *)
Lemma path_collapsible_isSet :
  forall A : U,
    path_collapsible A -> isSet A.
Proof.
  unfold path_collapsible, collapsible, const, isSet.
  intros A f x y p q.
  assert (Hp : p = cat (pr1' (f x y) p) (inv (pr1' (f y y) (refl y)))).
    destruct p. destruct (f x x). cbn. rewrite cat_inv_r. refl.
  assert (Hq : q = cat (pr1' (f x y) q) (inv (pr1' (f y y) (refl y)))).
    destruct q. destruct (f x x). cbn. rewrite cat_inv_r. refl.
  rewrite Hp, Hq. destruct (f x y) as [f' c]. cbn.
  rewrite (c p q). refl.
Defined.

(* Theorem 1 (Hedberg) *)
Lemma decidable_equality_isSet :
  forall A : U,
    decidable_equality A -> isSet A.
Proof.
  intros. apply path_collapsible_isSet.
  apply decidable_equality_path_collapsible.
  assumption.
Defined.

Lemma isSet_path_collapsible :
  forall A : U,
    isSet A -> path_collapsible A.
Proof.
  unfold isSet, path_collapsible, collapsible, const.
  intros A SA x y.
  exists id. intros p q. apply SA.
Defined.

Lemma isProp_collapsible :
  ~ forall A : U,
      isProp (collapsible A).
Proof.
  unfold isProp, collapsible, const.
  intros X.
  assert (H1 : const (fun b : bool => true)).
    compute. refl.
  assert (H2 : const (fun b : bool => false)).
    compute. refl.
  specialize (X bool (| _, H1 |) (| _, H2 |)).
  apply sigma_eq_elim in X. cbn in X. destruct X as [p _].
  apply neq_false_true. exact (inv (happly p true)).
Defined.

(*
Lemma isProp_path_collapsible :
  forall A : U,
    isProp (path_collapsible A).
Proof.
  unfold isProp, path_collapsible, collapsible, const.
  intros A f g.
  apply funext. intro x. apply funext. intro y.
  apply sigma_eq_intro. esplit.
Unshelve.
  Focus 2. destruct (f x y) as [f' cf], (g x y) as [g' cg]. cbn.
    apply funext. intro p. apply path_collapsible_isSet. exact f.
  repeat (apply funext; intro).
  destruct (f x y), (g x y). cbn.
    rewrite transport_pi.
  apply path_collapsible_isSet. apply f.

Lemma equiv_path_collapsible_isSet :
  path_collapsible = isSet.
Proof.
  apply funext. intro A. apply ua. unfold equiv.
  exists (path_collapsible_isSet A).
  apply qinv_isequiv. unfold qinv.
  exists (isSet_path_collapsible A).
  unfold homotopy, comp, id; split.
    intro SA. repeat (apply funext; intro). apply isSet_type1. assumption.
    unfold path_collapsible, collapsible, const, isSet_path_collapsible,
      path_collapsible_isSet.
      intros. repeat (apply funext; intro).
      apply sigma_eq_intro. esplit. Unshelve.
        Focus 2. cbn. destruct (x x0 x1) as [f c]. unfold id. apply funext.
          intro y. cbn. destruct y.
Abort.
*)

(* Definition 2 *)
Definition stable (A : U) : U :=
  ~ ~ A -> A.

Definition separated (A : U) : U :=
  forall x y : A, ~ ~ x = y -> x = y.

Lemma decidable_stable :
  forall A : U,
    decidable A -> stable A.
Proof.
  unfold decidable, stable. intros A [a | x] f.
    exact a.
    destruct (f x).
Defined.

Lemma stable_not_decidable :
  ~ forall A : U, stable A -> decidable A.
Proof.
Abort.

Lemma separated_path_collapsible :
  forall A : U,
    separated A -> path_collapsible A.
Proof.
  unfold separated, path_collapsible, collapsible, const.
  intros A s x y. esplit.
Unshelve.
  Focus 2. intro p. apply s. intro. destruct (X p).
  intros p q. cbn. apply ap. apply funext. intro. destruct (x0 p).
Defined.

(* Lemma 3 *)
Lemma separated_isSet :
  forall A : U,
    separated A -> isSet A.
Proof.
  intros A H. apply path_collapsible_isSet, separated_path_collapsible, H.
Defined.

(* Definition 3 *)
Print trunc_rec.
(* ===> forall A B : U, isProp B -> (A -> B) -> trunc A -> B *)

Lemma isProp_pCont :
  forall A : U,
    isProp (pCont A).
Proof.
  unfold pCont. intros A f g.
  apply funext. intro P. apply funext. intro PP. apply funext. intro h.
  apply PP.
Defined.

(*
Set Universe Polymorphism.

Section lift.

Universe i j.

Definition LiftProp (A : U@{i}) (PA : isProp A) : U@{j} :=
  Eval hnf in let enforce_lt := U@{i} : U@{j} in A.

End lift.
Axiom resize : forall {A : U}, isProp A -> U.
Axiom equiv_resize : forall (A : U) (PA : isProp A), resize PA = A.
Axiom resize_comp :
  forall (A : U) (PA : isProp A),
    resize PA = A.
*)

(* Proposition 1 *)
Lemma trunc_pCont :
  forall A : U,
    trunc A = pCont A.
Proof.
  intro. apply isProp_iff_eq.
    apply isProp_trunc.
    apply isProp_pCont.
    intro a. unfold pCont. intros P PP f. revert a. apply trunc_rec.
      assumption.
      exact f.
    intro a. eapply pCont_rec.
      apply isProp_trunc.
      apply trunc'.
      Fail exact a. (* Universe inconsistency *)
Admitted.

(* Definition 4 *)
Definition hstable (A : U) : U :=
  trunc A -> A.

Definition hseparated (A : U) : U :=
  forall x y : A, trunc (x = y) -> x = y.

Lemma isProp_hstable :
  ~ forall A : U, isProp (hstable A).
Proof.
  unfold isProp, hstable.
  intro f. specialize (f bool (fun _ => true) (fun _ => false)).
  apply happly in f.
    apply neq_false_true. apply inv. assumption.
    exact (trunc' false).
Defined.

Lemma separated_hseparated :
  forall A : U,
    separated A -> hseparated A.
Proof.
  unfold separated, hseparated.
  intros A f x y p. apply f. intro H.
  cut empty.
    destruct 1.
    revert p. apply trunc_rec.
      apply isProp_empty.
      intro p. destruct (H p).
Defined.

(* Theorem 2 *)
Lemma hseparated_path_collapsible :
  forall A : U,
    hseparated A -> path_collapsible A.
Proof.
  unfold hseparated, path_collapsible, collapsible.
  intros A hs x y.
  exists (fun p => hs _ _ (trunc' p)).
  compute. intros p q. apply ap, path.
Defined.

Lemma isSet_hseparated :
  forall A : U,
    isSet A -> hseparated A.
Proof.
  unfold isSet, hseparated.
  intros A SA x y p.
  revert p. apply trunc_rec.
    unfold isProp. apply SA.
    intro p. exact p.
Defined.

Lemma path_collapsible_hseparated :
  forall A : U,
    path_collapsible A -> hseparated A.
Proof.
  intros. apply isSet_hseparated, path_collapsible_isSet. assumption.
Defined.

Lemma hseparated_isSet :
  forall A : U,
    hseparated A -> isSet A.
Proof.
  intros. apply path_collapsible_isSet, hseparated_path_collapsible.
  assumption.
Defined.

(** Having propositional truncation gives us some extensionality, as we
    don't need functional extensionality to prove that separated types
    are h-separated. *)

(** * 4 Collapsibility implies H-Stability *)

Definition fixpoint {A : U} (f : A -> A) : U :=
  {x : A & x = f x}.

(* Proposition 3 *)
Lemma ap_const_aux :
  forall {A B : U} {f : A -> B} (c : const f) {x y : A} (p : x = y),
    ap f p = cat (c x y) (inv (c y y)).
Proof.
  destruct p. cbn. intros. rewrite cat_inv_r. refl.
Defined.

Lemma ap_const :
  forall {A B : U} {f : A -> B},
    const f -> forall {x : A} (p : x = x),
      ap f p = refl (f x).
Proof.
  intros A B f c x p. rewrite (ap_const_aux c p). apply cat_inv_r.
Defined.

Lemma inv_cat :
  forall {A : U} {x y z : A} (p : x = y) (q : y = z),
    inv (cat p q) = cat (inv q) (inv p).
Proof.
  destruct p, q. cbn. refl.
Defined.

(* Lemma 4 (Fixed Point Lemma) *)
Lemma isProp_fixpoint :
  forall (A : U) (f : A -> A),
    const f -> isProp (fixpoint f).
Proof.
  unfold const, isProp, fixpoint.
  intros A f c [x p] [y q].
  apply sigma_eq_intro. cbn.
  destruct (cat p (cat (c x y) (inv q))).
  exists (cat p (inv q)).
  rewrite transport_eq_fun, ap_id, (ap_const c), cat_refl_r, inv_cat,
          inv_inv, <- cat_assoc, cat_inv_l, cat_refl_r.
  refl.
Defined.

(* Theorem 3 *)
Lemma collapsible_hstable :
  forall {A : U},
    collapsible A -> hstable A.
Proof.
  unfold collapsible, const, hstable.
  intros A [f c] ta.
  cut (fixpoint f).
    exact pr1'.
    revert ta. apply trunc_rec.
      apply isProp_fixpoint. exact c.
      intro a. exists (f a). apply c.
Defined.

Lemma hstable_collapsible :
  forall {A : U},
    hstable A -> collapsible A.
Proof.
  unfold hstable, collapsible, const.
  intros A f.
  exists (fun x : A => f (trunc' x)).
  intros x y. apply ap, path.
Defined.

(** The authors claim that this is provable. *)
Lemma wut :
  LEM ->
    forall (A B : U) (f : A -> B) (c : const f),
      isSet B -> trunc A -> B.
Proof.
  unfold const, isSet. intros LEM A B f c SA ta.
  
  Search isSet. Print collapsible. Print separated.
  apply isSet_hseparated in SA.
  unfold hseparated in SA.
Abort.

(** * 5 Global Collapsibility implies Decidable Equality *)

(*
Goal
  hstable = collapsible.
Proof.
  apply funext. intro A.
  apply ua. unfold equiv.
  exists hstable_collapsible.
  apply qinv_isequiv. unfold qinv.
  exists collapsible_hstable.
  unfold homotopy, comp, id, hstable, collapsible, const; split.
    Focus 2. intro f. apply funext. intro x.
      compute. destruct (trunc_rec _). rewrite e. apply ap, path.
    intros [f c]. apply sigma_eq_intro. esplit. Unshelve.
      Focus 2. apply funext. intro x. cbn. destruct (trunc_rec _).
        cbn. rewrite e. apply c.
      rewrite transport_pi. cbn.
        apply funext. intro x. apply funext. intro y.
        rewrite transport_pi. rewrite transport_eq_fun.
Abort.
*)

Lemma not_everything_collapsible :
  ~ forall A : U, collapsible A.
Proof.
  Check not_Prop_making_functor trunc.
  intro H.
  assert (forall A : U, hstable A).
    intro. apply collapsible_hstable. apply H.
  apply (not_Prop_making_functor trunc).
    intros. apply path.
    exact (trunc' false).
    apply X.
Defined.

(* Lemma 5, my custom proof *)
Lemma lemma_5 :
  forall (A : U) (x y : A),
    (forall z : A, collapsible ((x = z) + (y = z))) ->
      decidable (x = y).
Proof.
  unfold collapsible, const, decidable.
  intros A x y H.
  pose (p := (| pr1' (H x) (inl (refl x)), pr2' (H x) (inl (refl x)) _ |)).
  destruct p as [e1 p].
  pose (q := (| pr1' (H y) (inr (refl y)), pr2' (H y) (inr (refl y)) _ |)).
  destruct q as [e2 q].
  destruct e1.
    destruct e2.
      left. exact e0.
      right. destruct 1. assert (inl e = inr e0).
        rewrite <- p, <- q. apply (pr2' (H x)).
        apply encode_sum in X. cbn in X. assumption.
    left. apply inv. exact e.
Defined.

(* Theorem 4 *)
Theorem all_collapsible_all_decidable_equality :
  (forall A : U, collapsible A) ->
  (forall A : U, decidable_equality A).
Proof.
  unfold decidable_equality.
  intros H A x y.
  apply lemma_5. intro. apply H.
Defined.

(** * 6 Populatedness *)

(* Definition 5 *)
Definition populated (A : U) : U :=
  forall f : A -> A, const f -> fixpoint f.

(* Proposition 4.1 *)
Definition make_populated {A : U} (x : A) : populated A :=
  fun (f : A -> A) (c : const f) =>
    (| f x, c x (f x) |).

(* Proposition 4.2 *)
Lemma isProp_populated :
  forall A : U,
    isProp (populated A).
Proof.
  unfold isProp, populated.
  intros A f g.
  apply funext. intro h. apply funext. intro c.
  apply isProp_fixpoint. assumption.
Defined.

Lemma trunc_populated :
  forall A : U,
    trunc A -> populated A.
Proof.
  unfold populated, const, fixpoint.
  intros A ta f c.
  revert ta. apply trunc_rec.
    apply isProp_fixpoint. assumption.
    intro a. exists (f a). apply c.
Defined.

(* Theorem 5 *)
Theorem populated_spec :
  forall A : U,
    populated A =
    forall P : U, isProp P -> (P -> A) -> (A -> P) -> P.
Proof.
  intro. apply isProp_iff_eq.
    apply isProp_populated.
    unfold isProp. intros f g. repeat (apply funext; intro).
      apply x0.
    unfold populated. intros H P PP f g. apply g.
      apply (H (fun x : A => f (g x))). intros x y.
      rewrite (PP (g x) (g y)). refl.
    intro H.
    assert (populated A).
      unfold populated, const, fixpoint. intros f c. apply H.
        apply isProp_fixpoint. exact c.
        exact pr1'.
        intro a. exists (f a). apply c. 
    assumption.
Defined.

Print Assumptions populated_spec.

(** * 7 Taboos and Counter-Models *)

Check @trunc'.
(* ===> @trunc' : forall A : U, A -> trunc A *)

Check trunc_populated.
(* ===> trunc_populated : forall A : U, trunc A -> populated A *)

Lemma populated_dbl_neg :
  forall A : U,
    populated A -> ~ ~ A.
Proof.
  unfold populated.
  intros A H f.
  assert (x : A).
    eapply (H (fun x => match f x with end)). intros x y. destruct (f x).
  destruct (f x).
Defined.

(** ** 7.1 Inhabited and H-Inhabited *)

Lemma not_all_hstable :
  ~ forall A : U, hstable A.
Proof.
  unfold hstable. apply not_Prop_making_functor.
    intros. apply path.
    exact (trunc' false).
Defined.

Lemma not_all_hstable' :
  ~ forall A : U, trunc A -> A.
Proof.
  intros. apply not_all_hstable.
Defined.

(* TODO: any relation has a functional subrelation. *)

(** ** 7.2 H-Inhabited and Populated *)

Definition ap2
  {A B C : U} (f : A -> B -> C) {x x' : A} {y y' : B}
  (p : x = x') (q : y = y') : f x y = f x' y'.
Proof.
  destruct p, q. refl.
Defined.

(* Lemma 6 *)
Lemma populated_hstable :
  forall A : U,
    populated (hstable A).
Proof.
  unfold populated, const, fixpoint, hstable.
  intros A f c. esplit.
Unshelve.
  Focus 2. intro ta. assert (fixpoint f).
    unfold fixpoint. revert ta. apply trunc_rec.
      apply isProp_fixpoint. exact c.
      intro a. exists (fun _ => f (fun _ => a) (trunc' a)).
        apply funext. intro x.
        rewrite <- (c (fun _ => a) (fun _ => f (fun _ => a) (trunc' a))).
        apply ap, path.
    exact (pr1' X ta).
  apply funext. intro ta. destruct (trunc_rec _). cbn. rewrite e.
    apply ap2. apply funext. intro. destruct (trunc_rec _).
      cbn. rewrite e, e0. rewrite (c x x1). refl.
      refl.
Defined.

Lemma not_all_populated_trunc :
  (forall A : U, populated A -> trunc A) ->
    forall A : U, trunc (hstable A).
Proof.
  intros H A. apply H. apply populated_hstable.
Defined.

(* Theorem 6 *)
Theorem theorem_6 :
  (forall A : U, populated A -> trunc A) =
  (forall A : U, trunc (trunc A -> A)).
Proof.
  apply isProp_iff_eq.
    intros f g. repeat (apply funext; intro). apply path.
    intros f g. repeat (apply funext; intro). apply path.
    intros H A. apply H. apply populated_hstable.
    intros H A PA.
      specialize (H A). revert H. apply trunc_rec.
        apply isProp_trunc.
        intro f. unfold populated, const, fixpoint in PA.
        apply trunc'. eapply (pr1' (PA (fun x : A => f (trunc' x)) _)).
Unshelve.
  intros. cbn. apply ap, path.
Defined.

Lemma populated_spec' :
  forall A : U,
    populated A = (trunc (trunc A -> A) -> trunc A).
Proof.
  intro A.
  apply isProp_iff_eq.
    apply isProp_populated.
    apply isProp_fun, isProp_trunc.
    intro H. apply trunc_rec.
      apply isProp_trunc.
      intro f. unfold populated, const, fixpoint in H.
        apply trunc'. eapply (pr1' (H (fun x : A => f (trunc' x)) _)).
        Unshelve. Focus 2. intros. cbn. apply ap, path.
    unfold populated, const, fixpoint. intros H f c.
    assert (trunc (trunc A -> A)).
      apply trunc'. intro ta. assert (trunc (trunc A -> A)).
        revert ta. apply trunc_rec.
          apply isProp_trunc.
          intro x. apply trunc'. intros _. exact x.
      assert (fixpoint f).
        unfold fixpoint. revert X. apply trunc_rec.
          apply isProp_fixpoint. assumption.
          intro g. exists (f (g ta)). apply c.
        exact (pr1' X0).
    specialize (H X). revert H. apply trunc_rec.
      apply isProp_fixpoint. assumption.
      intro x. exists (f x). apply c.
Defined.

Lemma conclusion_of_theorem_6_is_propositional_axiom_of_choice :
  (forall A : U, trunc (trunc A -> A)) =
  (forall (P : U) (Y : P -> U), isProp P ->
    (forall p : P, trunc (Y p)) -> trunc (forall p : P, Y p)).
Proof.
  apply isProp_iff_eq.
    apply isProp_pi. intro. apply isProp_trunc.
    repeat (apply isProp_pi; intro). apply isProp_trunc.
    Focus 2. intros H A.
      specialize (H (trunc A) (fun _ => A) (isProp_trunc A)).
      cbn in H. apply H. exact id.
    intros H P Y PP f. specialize (H (forall p : P, Y p)).
      revert H. apply trunc_rec.
        apply isProp_trunc.
        intro. apply trunc'. intro. apply X.
          specialize (f p). revert f. apply trunc_rec.
            apply isProp_trunc.
            intro. apply trunc'. intro. rewrite (PP p0 p). assumption.
Defined.

(** ** 7.3 Populated and Non-Empty *)

(* Lemma 7 *)
Lemma dbl_neg_populated_LEM :
  (forall A : U, ~ ~ A -> populated A) -> LEM.
Proof.
  unfold populated, const, fixpoint, LEM.
  intros H P PP.
  eapply (pr1' (H _ _ _ _)).
Unshelve.
  intro. apply X. right. intro. apply X. left. assumption.
  exact id.
  intros. apply ex_3_7.
    assumption.
    apply isProp_fun, isProp_empty.
    intro. destruct X. destruct (n p).
Defined.

Print Assumptions dbl_neg_populated_LEM.