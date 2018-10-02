Add Rec LoadPath "/home/zeimer/Code/Coq/HoTT".

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

(** * Hedberg's Theorem *)

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

