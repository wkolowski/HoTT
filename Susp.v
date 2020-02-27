Axiom Susp : Type -> Type.
Axiom N : forall {A : Type}, Susp A.
Axiom S : forall {A : Type}, Susp A.
Axiom merid : forall {A : Type}, A -> @N A = @S A.

Arguments merid {A}.

Axiom Susp_rec :
  forall {A B : Type} (N' S' : B) (m : A -> N' = S'),
    Susp A -> B.

Axiom Susp_rec_comp_N :
  forall {A B : Type} (N' S' : B) (m : A -> N' = S'),
    Susp_rec N' S' m N = N'.

Axiom Susp_rec_comp_S :
  forall {A B : Type} (N' S' : B) (m : A -> N' = S'),
    Susp_rec N' S' m S = S'.

Axiom Susp_rec_comp_merid :
  forall {A B : Type} (N' S' : B) (m : A -> N' = S') (x : A),
    Susp_rec N' S' m (merid x) = m x.