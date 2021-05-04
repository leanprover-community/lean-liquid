import for_mathlib.arrow
import for_mathlib.Fintype.basic
import for_mathlib.Profinite.limits
import for_mathlib.Profinite.basic
import for_mathlib.Fintype.basic
import topology.locally_constant.basic
import category_theory.limits.functor_category
import for_mathlib.discrete_quotient

/-!
Let `X` and `Y` be profinite sets and `f : X ⟶ Y` a morphism.
We show:
1. That `X` is a limit of finite sets.
2. That `f` is a limit of morphisms of finite sets,
  when considered as an object in the arrow category.
-/

open_locale classical

universe u
open category_theory

noncomputable theory

namespace Profinite

section limit_rep

variables (X : Profinite.{u})

/-- The diagram indexed by `discrete_quotient X` whose limit is isomorphic to `X`. -/
def diagram : discrete_quotient X ⥤ Fintype.{u} :=
{ obj := λ I, Fintype.of I,
  map := λ I J h, discrete_quotient.of_le $ le_of_hom h }

/-- An abbreviation for `X.diagram ⋙ Fintype_to_Profinite`. -/
abbreviation diagram' : discrete_quotient X ⥤ Profinite :=
  X.diagram ⋙ Fintype_to_Profinite

/-- The limit cone exhibiting `X` as a limit of `X.diagram`. -/
def fincone : limits.cone X.diagram' :=
{ X := X,
  π := { app := λ I, ⟨I.proj, I.proj_continuous⟩ } }

instance is_iso_lift :
  is_iso ((limit_cone X.diagram').is_limit.lift X.fincone) :=
is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply discrete_quotient.eq_of_proj_eq,
    intros I,
    apply_fun (λ u, u.val I) at h,
    exact h },
  { let C := (limit_cone (X.diagram ⋙ Fintype_to_Profinite)).cone,
    rintros (x : C.X.to_Top),
    have := discrete_quotient.exists_of_compat (λ I : discrete_quotient X, x.val I) (λ I J f, _),
    { rcases this with ⟨x,hx⟩,
      refine ⟨x,_⟩,
      ext1, ext1 I,
      exact hx I },
    { change _ = C.π.app J _,
      erw ← C.w (hom_of_le f),
      refl } }
end

/-- 
The isomorphism of cones between `X.Fincone` and 
`limit_cone (X.diagram ⋙ Fintype_to_Profinite)`. 
-/
def fincone_iso : X.fincone ≅ (limit_cone _).cone :=
limits.cones.ext (as_iso $ (limit_cone _).is_limit.lift _) (λ _, rfl)

/-- 
`X.Fincone` is indeed a limit cone. 
-/
def fincone_is_limit : limits.is_limit X.fincone :=
limits.is_limit.of_iso_limit (limit_cone_cone_is_limit _) X.fincone_iso.symm

variables {X} {Y : Profinite.{u}}

/-- 
Change a cone over `Y.diagram ⋙ Fintype_to_Profinite` 
with respect to a morphism `f : X ⟶ Y`.
This is used to obtain the functorial properties of the `X.Fincone` constructions.
-/
def change_cone (f : Y ⟶ X) (C : limits.cone Y.diagram') :
  limits.cone (X.diagram ⋙ Fintype_to_Profinite) :=
{ X := C.X,
  π :=
  { app := λ I, C.π.app (I.comap f.continuous) ≫
    ⟨discrete_quotient.map (le_refl _), discrete_quotient.map_continuous _⟩,
    naturality' := begin
      intros I J g,
      ext1,
      have h : I.comap f.continuous ≤ J.comap f.continuous, by tidy,
      rw [← C.w (hom_of_le h)],
      dsimp [Fintype_to_Profinite, diagram] at *,
      erw [← discrete_quotient.map_of_le_apply, ← discrete_quotient.of_le_map_apply],
      refl,
    end } }

theorem change_cone_lift (f : Y ⟶ X) : f = X.fincone_is_limit.lift (change_cone f Y.fincone) :=
X.fincone_is_limit.uniq (change_cone f Y.fincone) f (λ i, rfl)

/-- Changing a cone by an identity morphism results in a cone isomorphic to the given one. -/
def change_cone_id (C : limits.cone (X.diagram ⋙ Fintype_to_Profinite)) :
  change_cone (𝟙 X) C ≅ C :=
limits.cones.ext (eq_to_iso rfl)
begin
  intros I,
  ext1,
  dsimp [change_cone] at *,
  suffices : C.π.app (I.comap continuous_id) x = C.π.app I x,
    by {erw [this, discrete_quotient.map_id], refl},
  congr, simp,
end

/-- The compatibility of `change_cone` with respect to composition of morphisms. -/
def change_cone_comp {Z : Profinite.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
  (C : limits.cone (Z.diagram ⋙ Fintype_to_Profinite)) :
  change_cone (g ≫ f) C ≅ change_cone f (change_cone g C) :=
limits.cones.ext (eq_to_iso rfl)
begin
  intros I,
  ext1,
  dsimp [change_cone] at *,
  rw (show C.π.app ((I.comap f.continuous).comap g.continuous) =
    C.π.app (I.comap (g ≫ f).continuous), by refl),
  change _ = (discrete_quotient.map _ ∘ discrete_quotient.map _) _,
  rw ← discrete_quotient.map_comp,
  refl,
end

end limit_rep

namespace arrow

variable (f : arrow Profinite.{u})

/-- 
A gadget used to show that any arrow in `Profinite` can be expressed as a 
limit of arrows of `Fintype`s. 
This will be used as the category indexing the limit.
-/
@[nolint has_inhabited_instance]
structure index_cat : Type u :=
(left : discrete_quotient f.left)
(right : discrete_quotient f.right)
(compat : discrete_quotient.le_rel f.hom.continuous left right)

namespace index_cat

variable {f}

/-- Morphisms for `index_cat`. -/
@[nolint has_inhabited_instance]
structure hom (A B : index_cat f) : Type u :=
(left : A.left ≤ B.left)
(right : A.right ≤ B.right)

instance : category (index_cat f) :=
{ hom := hom,
  id := λ A, ⟨le_refl _, le_refl _⟩,
  comp := λ A B C f g , ⟨le_trans f.left g.left, le_trans f.right g.right⟩,
  id_comp' := λ A B f, by {cases f, refl},
  comp_id' := λ A B f, by {cases f, refl},
  assoc' := λ A B C D f g h, by {cases f, cases g, cases h, refl} }

/-- 
Make a term of `index_cat` given a clopen cover of a target of the arrow.
This is done fuunctorially.
-/
def mk_right : discrete_quotient f.right ⥤ index_cat f :=
{ obj := λ I,
  { left := I.comap f.hom.continuous,
    right := I,
    compat := by tauto },
  map := λ I J f,
  { left := λ a b, (le_of_hom f) _ _,--clopen_cover.pullback_mono $ le_of_hom f,
    right := le_of_hom f } }

/-- 
Make a term of `index_cat` given a clopen cover of a source of the arrow.
This is done fuunctorially.
-/
def mk_left : discrete_quotient f.left ⥤ index_cat f :=
{ obj := λ I,
  { left := I,
    right := ⊤,
    compat := by tauto },
  map := λ I J f, { left := by tidy, right := by tauto } }

end index_cat

/-- 
The diagram whose limit is a given arrow in `Profinite`.
-/
def diagram : index_cat f ⥤ arrow Fintype.{u} :=
{ obj := λ A,
  { left := Fintype.of A.left,
    right := Fintype.of A.right,
    hom := discrete_quotient.map A.compat },
  map := λ A B g,
  { left := discrete_quotient.of_le g.left,
    right := discrete_quotient.of_le g.right } }

/-- An abbreviation for `diagram f ⋙ Fintype_to_Profinite.map_arrow`. -/
abbreviation diagram' : index_cat f ⥤ arrow Profinite := diagram f ⋙ Fintype_to_Profinite.map_arrow

/-- The diagram of profinite sets obtained from the sources of `diagram'`. -/
abbreviation left_diagram : index_cat f ⥤ Profinite := diagram' f ⋙ arrow.left_func

/-- The diagram of profinite sets obtained from the targets of `diagram'`. -/
abbreviation right_diagram : index_cat f ⥤ Profinite := diagram' f ⋙ arrow.right_func

/-- The usual limit cone over `diagram' f`. -/
def limit_cone : limits.limit_cone (diagram' f) :=
arrow.limit_cone _ (limit_cone $ left_diagram _) (limit_cone $ right_diagram _)

/-- 
The cone which we want to show is a limit cone of `diagram' f`.
Its cone point is the given arrow `f`.
-/
def fincone : limits.cone (diagram' f) :=
{ X := f,
  π :=
  { app := λ Is,
    { left := ⟨discrete_quotient.proj _, discrete_quotient.proj_continuous _⟩,
      right := ⟨discrete_quotient.proj _, discrete_quotient.proj_continuous _⟩ } } }

instance is_iso_lift_left : is_iso ((limit_cone f).is_limit.lift (fincone f)).left :=
is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply discrete_quotient.eq_of_proj_eq,
    intros I,
    apply_fun subtype.val at h,
    let II := index_cat.mk_left.obj I,
    apply_fun (λ f, f II) at h,
    exact h },
 { intros x,
    cases x with x hx,
    dsimp at *,
    let Us : Π (I : discrete_quotient f.left), I := λ U, x (index_cat.mk_left.obj U),
    rcases discrete_quotient.exists_of_compat Us _ with ⟨y,hy⟩,
    { refine ⟨y,_⟩,
      ext Is : 2,
      dsimp at *,
      change discrete_quotient.proj _ _ = _,
      have : x Is = Us Is.left,
      { let ff : Is ⟶ index_cat.mk_left.obj Is.left := ⟨le_refl _, by tauto⟩,
        dsimp [Us],
        rw ← hx ff,
        dsimp [Fintype_to_Profinite, diagram],
        simp },
      rw this,
      apply hy },
    { intros I J h,
      specialize hx (index_cat.mk_left.map $ hom_of_le h),
      exact hx } }
end

instance is_iso_lift_right : is_iso ((limit_cone f).is_limit.lift (fincone f)).right :=
is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply discrete_quotient.eq_of_proj_eq,
    intros I,
    apply_fun subtype.val at h,
    let II := index_cat.mk_right.obj I,
    apply_fun (λ f, f II) at h,
    change discrete_quotient.proj _ _ = discrete_quotient.proj _ _ at h,
    have hII : II.right ≤ I := le_refl _,
    erw [← discrete_quotient.of_le_proj_apply hII, h],
    simp },
  { intros x,
    cases x with x hx,
    let Us : Π (I : discrete_quotient f.right), I := λ U, x (index_cat.mk_right.obj U),
    rcases discrete_quotient.exists_of_compat Us _ with ⟨y,hy⟩,
    { refine ⟨y,_⟩,
      ext Is : 2,
      dsimp at *,
      change discrete_quotient.proj _ _ = _,
      have : x Is = Us Is.right,
      { let ff : Is ⟶ index_cat.mk_right.obj Is.right := ⟨_, by tauto⟩,
        { dsimp [Us],
          rw ← hx ff,
          dsimp [Fintype_to_Profinite, diagram],
          rcases (x Is),
          refl },
        { dsimp [index_cat.mk_right],
          apply Is.compat } },
      rw this,
      apply hy },
    { intros I J h,
      specialize hx (index_cat.mk_right.map $ hom_of_le h),
      exact hx } }
end

-- sanity check
example : is_iso ((limit_cone f).is_limit.lift (fincone f)) := by apply_instance

/-- The isomorphism between `Fincone f` and the cone of the limit cone `(limit_cone f)`. -/
def fincone_iso : fincone f ≅ (limit_cone f).cone :=
limits.cones.ext (as_iso ((limit_cone f).is_limit.lift (fincone f))) (λ I, rfl)

/-- `Fincone f` is indeed a limit cone. -/
def fincone_is_limit : limits.is_limit (fincone f) :=
limits.is_limit.of_iso_limit (limit_cone f).is_limit (fincone_iso f).symm

/--
If `f` is surjective, then the terms in the diagram whose limit is `f` are all surjective as well.
-/
lemma surjective_of_surjective (surj : function.surjective f.hom) (I : index_cat f) :
  function.surjective ((diagram f).obj I).hom :=
begin
  intros x,
  rcases discrete_quotient.proj_surjective _ x with ⟨x,rfl⟩,
  rcases surj x with ⟨y,rfl⟩,
  use discrete_quotient.proj _ y,
  refl,
end

end arrow

end Profinite
#lint
