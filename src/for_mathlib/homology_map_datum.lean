import for_mathlib.homology_iso_datum
import for_mathlib.composable_morphisms

noncomputable theory

universes v

open category_theory category_theory.category category_theory.limits

variables {C D : Type*} [category.{v} C] [category.{v} D] [abelian C] [abelian D]
  {S₁ S₂ : short_complex C} {H₁ H₂ : C}

--def homology.map_short_complex (φ : S₁ ⟶ S₂) :
--  S₁.homology ⟶ S₂.homology :=
--homology.map w₁ w₂ (arrow.hom_mk φ.comm₁₂.symm) (arrow.hom_mk φ.comm₂₃.symm) rfl

/-- Each S₁, S₂ is a sequence of two composable arrows, φ is a map (i.e. two
commutative squares) between S₁ and S₂. The datum given here allows to
compute the map in homology induced by φ: up to the identifications of the
homologies with H₁ and H₂ respectively, it is η. -/
structure homology_map_datum (φ : S₁ ⟶ S₂) (h₁ : homology_iso_datum S₁.1.f S₁.1.g H₁)
  (h₂ : homology_iso_datum S₂.1.f S₂.1.g H₂) (η : H₁ ⟶ H₂) :=
(κ : h₁.K ⟶ h₂.K) (fac₁' : h₁.f' ≫ κ = φ.τ₁ ≫ h₂.f') (fac₂' : κ ≫ h₂.ι = h₁.ι ≫ φ.τ₂)
(fac₃' : h₁.π ≫ η = κ ≫ h₂.π)

namespace homology_map_datum

restate_axiom fac₁'
restate_axiom fac₂'
restate_axiom fac₃'

attribute [reassoc] fac₁ fac₂ fac₃
local attribute [simp] fac₁ fac₂

variables (φ : S₁ ⟶ S₂) {h₁ : homology_iso_datum S₁.1.f S₁.1.g H₁}
  {h₂ : homology_iso_datum S₂.1.f S₂.1.g H₂} {η : H₁ ⟶ H₂}
variable (μ : homology_map_datum φ h₁ h₂ η)

@[simps]
def tautological' :
  homology_map_datum φ (homology_iso_datum.tautological' _ _ _)
    (homology_iso_datum.tautological' _ _ _)
    (short_complex.homology_functor.map φ) :=
{ κ := kernel.map _ _ _ _ φ.comm₂₃,
  fac₁' := begin
    ext,
    dsimp,
    simp only [assoc, kernel.lift_ι, kernel.lift_ι_assoc],
    exact φ.comm₁₂,
  end,
  fac₂' := by apply kernel.lift_ι,
  fac₃' := by apply homology.π'_map, }

variable {φ}

include μ

@[simps]
def map_exact_functor (F : C ⥤ D) [F.additive]
  [preserves_finite_limits F] [preserves_finite_colimits F] :
  homology_map_datum (F.map_short_complex.map φ) (h₁.apply_exact_functor F) (h₂.apply_exact_functor F) (F.map η) :=
{ κ := F.map μ.κ,
  fac₁' := by { dsimp, simp only [← F.map_comp, μ.fac₁], },
  fac₂' := by { dsimp, simp only [← F.map_comp, μ.fac₂], },
  fac₃' := by { dsimp, simp only [← F.map_comp, μ.fac₃], }, }

lemma homology_map_eq : short_complex.homology_functor.map φ =
  h₁.iso.inv ≫ η ≫ h₂.iso.hom := sorry

end homology_map_datum