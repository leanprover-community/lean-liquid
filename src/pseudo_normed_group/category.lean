import category_theory.concrete_category.bundled_hom

import pseudo_normed_group.profinitely_filtered

universe variables u

open category_theory

/-- The category of profinitely filtered pseudo normed groups with -/
def ProFiltPseuNormGrp : Type (u+1) :=
bundled profinitely_filtered_pseudo_normed_group

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

end ProFiltPseuNormGrp
