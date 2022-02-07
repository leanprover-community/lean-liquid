import category_theory.concrete_category.bundled_hom
import topology.category.Profinite
import data.equiv.fin
--import for_mathlib.concrete
import for_mathlib.CompHaus
import for_mathlib.topology

import pseudo_normed_group.with_Tinv

/-!

# The category of profinitely filtered pseudo-normed groups.

The category of profinite pseudo-normed groups, and the category of
profinitely filtered pseudo-normed groups equipped with an action of T⁻¹.

-/
universe variables u

open category_theory
open_locale nnreal

local attribute [instance] type_pow

noncomputable theory

/-- The category of CompHaus-ly filtered pseudo-normed groups. -/
def CompHausFiltPseuNormGrp : Type (u+1) :=
bundled comphaus_filtered_pseudo_normed_group

namespace CompHausFiltPseuNormGrp

def bundled_hom : bundled_hom @comphaus_filtered_pseudo_normed_group_hom :=
⟨@comphaus_filtered_pseudo_normed_group_hom.to_fun,
 @comphaus_filtered_pseudo_normed_group_hom.id,
 @comphaus_filtered_pseudo_normed_group_hom.comp,
 @comphaus_filtered_pseudo_normed_group_hom.coe_inj⟩

local attribute [instance] bundled_hom
attribute [derive [large_category, concrete_category]] CompHausFiltPseuNormGrp

instance : has_coe_to_sort CompHausFiltPseuNormGrp Type* := bundled.has_coe_to_sort

instance (M : CompHausFiltPseuNormGrp) : comphaus_filtered_pseudo_normed_group M := M.str

/-- Construct a bundled `CompHausFiltPseuNormGrp` from the underlying type and typeclass. -/
def of (M : Type u) [comphaus_filtered_pseudo_normed_group M] : CompHausFiltPseuNormGrp :=
bundled.of M

end CompHausFiltPseuNormGrp
