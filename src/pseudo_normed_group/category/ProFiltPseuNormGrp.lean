import pseudo_normed_group.category.strictCompHausFiltPseuNormGrp

universe variables u

open category_theory
open_locale nnreal

noncomputable theory

local attribute [instance] type_pow

/-- The category of profinitely filtered pseudo-normed groups. -/
def ProFiltPseuNormGrp : Type (u+1) :=
bundled profinitely_filtered_pseudo_normed_group

namespace ProFiltPseuNormGrp

local attribute [instance] CompHausFiltPseuNormGrp.bundled_hom

def bundled_hom : bundled_hom.parent_projection
  @profinitely_filtered_pseudo_normed_group.to_comphaus_filtered_pseudo_normed_group := ⟨⟩

local attribute [instance] bundled_hom

attribute [derive [large_category, concrete_category]] ProFiltPseuNormGrp

instance : has_coe_to_sort ProFiltPseuNormGrp Type* := bundled.has_coe_to_sort

instance : has_forget₂ ProFiltPseuNormGrp CompHausFiltPseuNormGrp := bundled_hom.forget₂ _ _

@[simps]
def to_CompHausFilt : ProFiltPseuNormGrp ⥤ CompHausFiltPseuNormGrp := forget₂ _ _

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
