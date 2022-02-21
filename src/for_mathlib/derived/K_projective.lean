import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import for_mathlib.derived.homological
import category_theory.abelian.projective

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

namespace homotopy_category
universes v u
variables {A : Type u} [category.{v} A] [abelian A]

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)
local notation `HH` := homotopy_category.homology_functor A (complex_shape.up ℤ) 0

class is_acyclic (X : 𝒦) : Prop :=
(cond [] : ∀ i, is_zero ((homotopy_category.homology_functor _ _ i).obj X))

lemma is_acyclic_of_iso {X Y : 𝒦} (e : X ≅ Y) [is_acyclic X] : is_acyclic Y :=
begin
  constructor,
  intros i,
  let e' : (homology_functor A (complex_shape.up ℤ) i).obj X ≅
    (homology_functor A (complex_shape.up ℤ) i).obj Y :=
    functor.map_iso _ e,
  apply is_zero_of_iso_of_zero _ e',
  apply is_acyclic.cond X i,
end

class is_K_projective (X : 𝒦) : Prop :=
(cond : ∀ (Y : 𝒦) [is_acyclic Y] (f : X ⟶ Y), f = 0)

class is_quasi_iso {X Y : 𝒦} (f : X ⟶ Y) : Prop :=
(cond : ∀ i, is_iso ((homotopy_category.homology_functor _ _ i).map f))

-- Move this
instance homology_functor_additive : functor.additive HH := functor.additive.mk $
begin
  rintros X Y ⟨f⟩ ⟨g⟩,
  dsimp [homotopy_category.homology_functor],
  erw ← (_root_.homology_functor _ _ _).map_add,
  refl,
  apply_instance,
end

instance homology_functor_homological : homological_functor HH := sorry

/--
If `A → B → C → A[1]` is a distinguished triangle, and `A → B` is a quasi-isomorphism,
then `C` is acyclic.
-/
lemma is_acyclic_of_dist_triang_of_is_quasi_iso (T : triangle 𝒦) (hT : T ∈ dist_triang 𝒦)
  [is_quasi_iso T.mor₁] : is_acyclic T.obj₃ := sorry

lemma hom_K_projective_bijective {X Y : 𝒦} (P : 𝒦) [is_K_projective P]
  (f : X ⟶ Y) [is_quasi_iso f] : function.bijective (λ e : P ⟶ X, e ≫ f) :=
begin
  /-
  Steps:
  1. Complete `f` to a dist triang `X → Y → Z → X[1]`.
  2. Use LES assoc. to `Hom(P,-)`, proved in `for_mathlib/derived/homological.lean`.
  3. Use lemma above + def of K-projective to see that `Hom(P,Z) = 0`.
  -/
  sorry
end

variable [enough_projectives A]
noncomputable theory

-- Main theorem about existence of K-projective replacements.
-- Perhaps all we need is this for bounded complexes, in which case we should
-- add an additional typeclass parameter here.
theorem exists_K_projective_replacement (X : 𝒦) :
  ∃ (P : 𝒦) [is_K_projective P] (f : P ⟶ X), is_quasi_iso f := sorry

def replace (X : 𝒦) : 𝒦 := (exists_K_projective_replacement X).some

instance (X : 𝒦) : is_K_projective X.replace :=
(exists_K_projective_replacement X).some_spec.some

def π (X : 𝒦) : X.replace ⟶ X :=
(exists_K_projective_replacement X).some_spec.some_spec.some

instance (X : 𝒦) : is_quasi_iso X.π :=
(exists_K_projective_replacement X).some_spec.some_spec.some_spec

def lift {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  P ⟶ X :=
((hom_K_projective_bijective P g).2 f).some

@[simp, reassoc]
lemma lift_lifts {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  lift f g ≫ g = f :=
((hom_K_projective_bijective P g).2 f).some_spec

lemma lift_unique {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g]
  (e : P ⟶ X) (h : e ≫ g = f) : e = lift f g :=
begin
  apply (hom_K_projective_bijective P g).1,
  simpa,
end

lemma lift_ext {P X Y : 𝒦} [is_K_projective P] (g : X ⟶ Y) [is_quasi_iso g]
  (a b : P ⟶ X) (h : a ≫ g = b ≫ g) : a = b :=
(hom_K_projective_bijective P g).1 h

@[simps]
def Ext0 : 𝒦ᵒᵖ ⥤ 𝒦 ⥤ Ab :=
{ obj := λ X, preadditive_yoneda.flip.obj (opposite.op $ X.unop.replace),
  map := λ X₁ X₂ f, preadditive_yoneda.flip.map (lift (X₂.unop.π ≫ f.unop) X₁.unop.π).op,
  map_id' := begin
    intros X,
    ext Y e,
    dsimp,
    simp only [category.comp_id, id_apply],
    convert category.id_comp _,
    symmetry,
    apply lift_unique,
    simp,
  end,
  map_comp' := begin
    intros X₁ X₂ X₃ f g,
    ext Y e,
    dsimp,
    simp only [comp_apply, linear_map.to_add_monoid_hom_coe,
      preadditive_yoneda_obj_map_apply, quiver.hom.unop_op, ← category.assoc],
    congr' 1,
    symmetry,
    apply lift_unique,
    simp,
  end } .

def Ext (i : ℤ) : 𝒦ᵒᵖ ⥤ 𝒦 ⥤ Ab :=
Ext0 ⋙ (whiskering_left _ _ _).obj (shift_functor _ i)

end homotopy_category
