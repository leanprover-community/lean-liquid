import laurent_measures.ses
import laurent_measures.condensed
import real_measures.condensed
import condensed.exact

universe u

noncomputable theory

open category_theory

open_locale nnreal

namespace laurent_measures

open laurent_measures_ses ProFiltPseuNormGrpWithTinv₁

section phi

variables (r : ℝ≥0) [fact (0 < r)]

/-- This doesn't work! We need to rescale the domain! -/
def Φ_profinite : profinite r ⋙ to_CompHausFiltPseuNormGrp₁.{u} r ⟶
  profinite r ⋙ to_CompHausFiltPseuNormGrp₁.{u} r :=
sorry

def Φ_condensed_nat_trans : condensed r ⟶ condensed r :=
whisker_right (Φ_profinite r) (CompHausFiltPseuNormGrp₁.to_Condensed)

def Φ_condensed (S : Profinite.{u}) :
  (condensed r).obj S ⟶ (condensed r).obj S :=
(Φ_condensed_nat_trans r).app S

lemma mono (S : Profinite.{u}) : mono (Φ_condensed r S) :=
sorry

end phi

section theta

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p

def Θ (S : Fintype.{u}) :
  (fintype_functor.{u} r ⋙ to_CompHausFiltPseuNormGrp₁.{u} r).obj S ⟶
  (real_measures.functor p).obj S :=
strict_comphaus_filtered_pseudo_normed_group_hom.mk' (θ_to_add p)
begin
  intro c,
  use θ_bound' p c,
  convert continuous_θ_c p S c,
  simp only [θ_c, one_mul, eq_mpr_eq_cast, set_coe_cast],
  refl,
end

def Θ_fintype_nat_trans :
  (fintype_functor.{u} r ⋙ to_CompHausFiltPseuNormGrp₁.{u} r) ⟶ (real_measures.functor.{u} p) :=
{ app := λ S, Θ p S,
  naturality' := λ S T f, by { ext x t, apply θ_natural, } }
.

def Θ_profinite : profinite r ⋙ to_CompHausFiltPseuNormGrp₁.{u} r ⟶
    real_measures.profinite.{u} p :=
(profinite_comp_to_CompHausFiltPseuNormGrp₁ r).hom ≫
  Profinite.extend_nat_trans (Θ_fintype_nat_trans.{u} p)
.

def Θ_condensed_nat_trans :
  condensed r ⟶ real_measures.condensed p :=
whisker_right (Θ_profinite p) (CompHausFiltPseuNormGrp₁.to_Condensed)

def Θ_condensed (S : Profinite.{u}) :
  (condensed r).obj S ⟶ (real_measures.condensed p).obj S :=
(Θ_condensed_nat_trans p).app S

lemma epi (S : Profinite.{u}) : epi (Θ_condensed r S) :=
sorry

end theta

section ses

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p

open CompHausFiltPseuNormGrp₁

-- lemma exact_with_constant_fintype :
--   ∃ C ≥ 1, ∀ S, exact_with_constant ((Φ_profinite r).app S) ((Θ p).app S) C :=
-- sorry

lemma exact_with_constant_profinite (S : Profinite) :
  ∃ C ≥ 1, exact_with_constant ((Φ_profinite r).app S) ((Θ_profinite p).app S) C :=
begin
  sorry
end

lemma exact (S : Profinite) : exact (Φ_condensed r S) (Θ_condensed p S) :=
begin
  obtain ⟨C, hC, H⟩ := exact_with_constant_profinite p S,
  exact condensed.exact_of_exact_with_constant _ _ C hC H,
end

end ses

end laurent_measures
