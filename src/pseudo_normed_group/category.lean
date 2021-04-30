import category_theory.concrete_category.bundled_hom
import topology.category.Profinite

import pseudo_normed_group.with_Tinv

/-!

# The category of profinitely filtered pseudo normed groups.

The category of profinite pseudo-normed groups, and the category of
profinitely filtered pseudo-normed groups equipped with an action of T⁻¹.

-/
universe variables u

open category_theory
open_locale nnreal

/-- The category of profinitely filtered pseudo normed groups. -/
def ProFiltPseuNormGrp : Type (u+1) :=
bundled profinitely_filtered_pseudo_normed_group

/-- The category of profinitely filtered pseudo normed groups with action of `T⁻¹`. -/
def ProFiltPseuNormGrpWithTinv (r : ℝ≥0) : Type (u+1) :=
bundled (@profinitely_filtered_pseudo_normed_group_with_Tinv r)

namespace ProFiltPseuNormGrp

instance bundled_hom : bundled_hom @profinitely_filtered_pseudo_normed_group_hom :=
⟨@profinitely_filtered_pseudo_normed_group_hom.to_fun,
 @profinitely_filtered_pseudo_normed_group_hom.id,
 @profinitely_filtered_pseudo_normed_group_hom.comp,
 @profinitely_filtered_pseudo_normed_group_hom.coe_inj⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] ProFiltPseuNormGrp

/-- Construct a bundled `ProFiltPseuNormGrp` from the underlying type and typeclass. -/
def of (M : Type u) [profinitely_filtered_pseudo_normed_group M] : ProFiltPseuNormGrp :=
bundled.of M

instance : has_zero ProFiltPseuNormGrp := ⟨of punit⟩

instance : inhabited ProFiltPseuNormGrp := ⟨0⟩

instance (M : ProFiltPseuNormGrp) : profinitely_filtered_pseudo_normed_group M := M.str

@[simp] lemma coe_of (V : Type u) [profinitely_filtered_pseudo_normed_group V] : (ProFiltPseuNormGrp.of V : Type u) = V := rfl

@[simp] lemma coe_id (V : ProFiltPseuNormGrp) : ⇑(𝟙 V) = id := rfl

@[simp] lemma coe_comp {A B C : ProFiltPseuNormGrp} (f : A ⟶ B) (g : B ⟶ C) :
  ⇑(f ≫ g) = g ∘ f := rfl

@[simp] lemma coe_comp_apply {A B C : ProFiltPseuNormGrp} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
  (f ≫ g) x = g (f x) := rfl

open pseudo_normed_group

section

variables (M : Type*) [profinitely_filtered_pseudo_normed_group M] (c : ℝ≥0)

instance : t2_space (Top.of (filtration M c)) := by { dsimp, apply_instance }
instance : totally_disconnected_space (Top.of (filtration M c)) := by { dsimp, apply_instance }
instance : compact_space (Top.of (filtration M c)) := by { dsimp, apply_instance }

end

end ProFiltPseuNormGrp

namespace ProFiltPseuNormGrpWithTinv

variables (r' : ℝ≥0)

instance bundled_hom : bundled_hom (@profinitely_filtered_pseudo_normed_group_with_Tinv_hom r') :=
⟨@profinitely_filtered_pseudo_normed_group_with_Tinv_hom.to_fun r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.id r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.comp r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.coe_inj r'⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] ProFiltPseuNormGrpWithTinv

/-- Construct a bundled `ProFiltPseuNormGrpWithTinv` from the underlying type and typeclass. -/
def of (r' : ℝ≥0) (M : Type u) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  ProFiltPseuNormGrpWithTinv r' :=
bundled.of M

instance : has_zero (ProFiltPseuNormGrpWithTinv r') :=
⟨{ α := punit, str := punit.profinitely_filtered_pseudo_normed_group_with_Tinv r' }⟩

instance : inhabited (ProFiltPseuNormGrpWithTinv r') := ⟨0⟩

instance (M : ProFiltPseuNormGrpWithTinv r') :
  profinitely_filtered_pseudo_normed_group_with_Tinv r' M := M.str

@[simp] lemma coe_of (V : Type u) [profinitely_filtered_pseudo_normed_group_with_Tinv r' V] :
  (ProFiltPseuNormGrpWithTinv.of r' V : Type u) = V := rfl

@[simp] lemma of_coe (M : ProFiltPseuNormGrpWithTinv r') : of r' M = M :=
by { cases M, refl }

@[simp] lemma coe_id (V : ProFiltPseuNormGrpWithTinv r') : ⇑(𝟙 V) = id := rfl

@[simp] lemma coe_comp {A B C : ProFiltPseuNormGrpWithTinv r'} (f : A ⟶ B) (g : B ⟶ C) :
  ⇑(f ≫ g) = g ∘ f := rfl

@[simp] lemma coe_comp_apply {A B C : ProFiltPseuNormGrpWithTinv r'} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
  (f ≫ g) x = g (f x) := rfl
open pseudo_normed_group

section

variables (M : Type*) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] (c : ℝ≥0)
include r'

instance : t2_space (Top.of (filtration M c)) := by { dsimp, apply_instance }
instance : totally_disconnected_space (Top.of (filtration M c)) := by { dsimp, apply_instance }
instance : compact_space (Top.of (filtration M c)) := by { dsimp, apply_instance }

end

-- @[simps] def Filtration (c : ℝ≥0) : ProFiltPseuNormGrp ⥤ Profinite :=
-- { obj := λ M, ⟨Top.of (filtration M c)⟩,
--   map := λ M₁ M₂ f, ⟨f.level c, f.level_continuous c⟩,
--   map_id' := by { intros, ext, refl },
--   map_comp' := by { intros, ext, refl } }


open pseudo_normed_group profinitely_filtered_pseudo_normed_group_with_Tinv_hom

open profinitely_filtered_pseudo_normed_group_with_Tinv (Tinv)

variables {r'}
variables {M M₁ M₂ : ProFiltPseuNormGrpWithTinv.{u} r'}
variables {f : M₁ ⟶ M₂}

/-- The isomorphism induced by a bijective `profinitely_filtered_pseudo_normed_group_with_Tinv_hom`
whose inverse is strict. -/
def iso_of_equiv_of_strict (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
  M₁ ≅ M₂ :=
{ hom := f,
  inv := inv_of_equiv_of_strict e he strict,
  hom_inv_id' := by { ext x, simp [inv_of_equiv_of_strict, he] },
  inv_hom_id' := by { ext x, simp [inv_of_equiv_of_strict, he] } }

@[simp]
lemma iso_of_equiv_of_strict.apply (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) (x : M₁) :
  (iso_of_equiv_of_strict e he strict).hom x = f x := rfl

@[simp]
lemma iso_of_equiv_of_strict_symm.apply (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) (x : M₂) :
  (iso_of_equiv_of_strict e he strict).symm.hom x = e.symm x := rfl

def iso_of_equiv_of_strict'
  (e : M₁ ≃+ M₂)
  (strict' : ∀ c x, x ∈ filtration M₁ c ↔ e x ∈ filtration M₂ c)
  (continuous' : ∀ c, continuous (pseudo_normed_group.level e (λ c x, (strict' c x).1) c))
  (map_Tinv' : ∀ x, e (Tinv x) = Tinv (e x)) :
  M₁ ≅ M₂ :=
@iso_of_equiv_of_strict r' M₁ M₂
 {to_fun := e,
  strict' := λ c x, (strict' c x).1,
  continuous' := continuous',
  map_Tinv' := map_Tinv',
  ..e.to_add_monoid_hom } e (λ _, rfl)
  (by { intros c x hx, rwa [strict', e.apply_symm_apply] })

end ProFiltPseuNormGrpWithTinv
