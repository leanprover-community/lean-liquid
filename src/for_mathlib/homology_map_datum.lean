import for_mathlib.homology_iso_datum
import for_mathlib.short_complex

noncomputable theory

universes v

open category_theory category_theory.category category_theory.limits

variables {C D : Type*} [category.{v} C] [category.{v} D] [abelian C] [abelian D]
  {S₁ S₂ : short_complex C} {H₁ H₂ : C}

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
  h₁.iso.inv ≫ η ≫ h₂.iso.hom :=
begin
  simp only [short_complex.homology_functor_map, homology_iso_datum.iso_inv,
    homology_iso_datum.iso_hom, ← cancel_epi h₁.iso₁.hom,
    ← cancel_mono (homology.ι _ _ S₂.2), ← cancel_epi (homology.π' _ _ S₁.2), assoc,
    homology.map_ι, homology.π'_ι_assoc, cokernel.π_desc, assoc],
  erw [homology.lift_ι, homology.π'_desc'_assoc, assoc, μ.fac₃_assoc,
    h₁.iso₁_hom_kernel_ι_assoc, ← μ.fac₂_assoc, h₁.iso₁.hom_inv_id_assoc,
    ← h₂.cokernel_π_iso₂_inv_assoc, h₂.iso₂.inv_hom_id_assoc,
    h₂.cokernel_f'_eq_π_iso₂_hom],
  congr' 1,
  simp only [← cancel_epi h₂.iso₁.inv, ← h₂.iso₁_hom_kernel_ι, assoc, h₂.iso₁.inv_hom_id_assoc,
    ← h₂.has_homology.π_ι, h₂.has_homology_π, h₂.has_homology_ι],
end

end homology_map_datum

namespace homology_iso_datum

/-- If we understand the homology of `S`, then we should understand what is the
homology map of the morphism `F.map_short_complex S ⟶ G.map_short_complex S`
given by a natural transformation `φ : F ⟶ G` between exact functors -/
def map_nat_trans {S : short_complex C} {H : C} (h : homology_iso_datum S.1.f S.1.g H)
  {F G : C ⥤ D} [F.additive] [G.additive]
  [preserves_finite_limits F] [preserves_finite_colimits F]
  [preserves_finite_limits G] [preserves_finite_colimits G]
  (φ : F ⟶ G) : homology_map_datum (φ.map_short_complex.app S)
    (h.apply_exact_functor F) (h.apply_exact_functor G) (φ.app H) :=
{ κ := φ.app _,
  fac₁' := nat_trans.naturality _ _,
  fac₂' := (nat_trans.naturality _ _).symm,
  fac₃' := nat_trans.naturality _ _, }

end homology_iso_datum

namespace homology_map_datum

def of_g_are_zeros (φ : S₁ ⟶ S₂) (hg₁ : S₁.1.g = 0) (hg₂ : S₂.1.g = 0) :
  homology_map_datum φ (homology_iso_datum.of_g_is_zero S₁.1.f S₁.1.g hg₁)
    (homology_iso_datum.of_g_is_zero S₂.1.f S₂.1.g hg₂)
    (cokernel.map _ _ φ.τ₁ φ.τ₂ φ.comm₁₂) :=
{ κ := φ.τ₂,
  fac₁' := φ.comm₁₂,
  fac₂' := by { dsimp, simp only [comp_id, id_comp], },
  fac₃' := by { dsimp, simp only [cokernel.π_desc], }, }
end homology_map_datum
