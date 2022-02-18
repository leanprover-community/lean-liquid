import laurent_measures.ses
import laurent_measures.condensed
import real_measures.condensed
import condensed.exact

universe u

noncomputable theory

open category_theory

open_locale nnreal

namespace laurent_measures

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]

local notation `r` := @r p


open laurent_measures_ses

def Θ (S : Fintype.{u}) :
  (fintype_functor.{u u} r ⋙
    ProFiltPseuNormGrpWithTinv₁.to_CompHausFiltPseuNormGrp₁.{u u} r).obj S ⟶
  (real_measures.functor p).obj S :=
strict_comphaus_filtered_pseudo_normed_group_hom.mk' (θ_to_add)
begin
  intro c,
  use θ_bound' c,
  convert continuous_θ_c S c,
  simp only [θ_c, one_mul, eq_mpr_eq_cast, set_coe_cast],
  refl,
end

def Θ_fintype_nat_trans :
  (fintype_functor.{u u} r ⋙
    ProFiltPseuNormGrpWithTinv₁.to_CompHausFiltPseuNormGrp₁.{u u} r) ⟶
  (real_measures.functor p) :=
{ app := λ S, Θ p S,
  naturality' := λ S T f, by { ext x t, apply θ_natural, } }

def Θ_condensed (S : Profinite.{u}) :
  (condensed r).obj S ⟶ (real_measures.condensed p).obj S :=
sorry

end laurent_measures
