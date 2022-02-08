import pseudo_normed_group.category.strictProFiltPseuNormGrp

universe variables u

open category_theory
open_locale nnreal

local attribute [instance] type_pow

noncomputable theory

/-- The category of profinitely filtered pseudo-normed groups with action of `T⁻¹`. -/
def CompHausFiltPseuNormGrpWithTinv (r : ℝ≥0) : Type (u+1) :=
bundled (@comphaus_filtered_pseudo_normed_group_with_Tinv r)

namespace CompHausFiltPseuNormGrpWithTinv

variables (r' : ℝ≥0)

def bundled_hom : bundled_hom (@comphaus_filtered_pseudo_normed_group_with_Tinv_hom r') :=
⟨@comphaus_filtered_pseudo_normed_group_with_Tinv_hom.to_fun r',
 @comphaus_filtered_pseudo_normed_group_with_Tinv_hom.id r',
 @comphaus_filtered_pseudo_normed_group_with_Tinv_hom.comp r',
 @comphaus_filtered_pseudo_normed_group_with_Tinv_hom.coe_inj r'⟩

local attribute [instance] bundled_hom

attribute [derive [λ α, has_coe_to_sort α (Sort*), large_category, concrete_category]]
  CompHausFiltPseuNormGrpWithTinv

end CompHausFiltPseuNormGrpWithTinv
