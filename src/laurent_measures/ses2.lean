import laurent_measures.ses
import laurent_measures.condensed
import real_measures.condensed
import condensed.exact
import condensed.rescale

universe u

noncomputable theory

open category_theory

open_locale nnreal

lemma fact0lt3 : fact ((0 : ℝ≥0) < 3) := ⟨by norm_num⟩
local attribute [instance] fact0lt3

namespace laurent_measures

open laurent_measures_ses ProFiltPseuNormGrpWithTinv₁

section phi

variables (r : ℝ≥0) [fact (0 < r)] [fact (r ≤ 1)]

abbreviation finCHFPNG₁ :=
fintype_functor r ⋙ to_CompHausFiltPseuNormGrp₁.{u} r

abbreviation CHFPNG₁ :=
profinite r ⋙ to_CompHausFiltPseuNormGrp₁.{u} r

def Φ_finite_rescaled :
  finCHFPNG₁.{u} r ⋙ CompHausFiltPseuNormGrp₁.rescale.{u u} 3 ⟶ finCHFPNG₁.{u} r :=
{ app := λ S, comphaus_filtered_pseudo_normed_group_hom.strictify
    ((finCHFPNG₁ r).obj S) _ (Φ S) _ (Φ_bound_by_3 S),
  naturality' := λ S T f, sorry }

-- move this
instance rescale_preserves_limits' (r : ℝ≥0) [fact (0 < r)] :
  limits.preserves_limits.{u u u+1 u+1}
  (CompHausFiltPseuNormGrp₁.rescale.{u u} r) :=
sorry

-- move this
instance rescale_preserves_limits_of_shape_discrete_quotient (X : Profinite.{u}) :
  limits.preserves_limits_of_shape.{u u u u u+1 u+1} (discrete_quotient X)
    (to_CompHausFiltPseuNormGrp₁ r ⋙ CompHausFiltPseuNormGrp₁.rescale.{u u} 3) :=
limits.comp_preserves_limits_of_shape _ _

/-- This doesn't work! We need to rescale the domain! -/
def Φ_profinite_rescaled := Profinite.extend_nat_trans (Φ_finite_rescaled r)

def Φ_condensed_rescaled :=
whisker_right (Φ_profinite_rescaled r) (CompHausFiltPseuNormGrp₁.to_Condensed)

---- NOTE: this is the wrong approach, we need to reduce to finite `S`
-- instance mono_aux (S : Profinite.{u}) :
--   mono ((CompHausFiltPseuNormGrp₁.to_PNG₁.{u} ⋙ PseuNormGrp₁.to_Ab.{u}).map
--     ((Φ_profinite_rescaled.{u} r).app S)) :=
-- begin
--   rw [AddCommGroup.mono_iff_ker_eq_bot, eq_bot_iff],
--   intros x hx,
--   rw add_subgroup.mem_bot,
--   dsimp at hx, sorry,
-- end

lemma mono (S : Profinite.{u}) : mono ((Φ_condensed_rescaled r).app S) :=
begin
---- NOTE: this is the wrong approach, we need to reduce to finite `S`
  -- refine condensed.mono_to_Condensed_map _
  sorry
end

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

def Θ_profinite : profiniteCH r ⟶ real_measures.profinite.{u} p :=
Profinite.extend_nat_trans (Θ_fintype_nat_trans.{u} p)
.

def Θ_condensed :
  condensedCH r ⟶ real_measures.condensed p :=
whisker_right (Θ_profinite p) (CompHausFiltPseuNormGrp₁.to_Condensed)

---- NOTE: this is the wrong approach, we need to reduce to finite `S`
-- instance epi_aux  (S : Profinite.{u}) :
--   epi ((CompHausFiltPseuNormGrp₁.to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map ((Θ_profinite r).app S)) :=
-- sorry

lemma epi (S : Profinite.{u}) : epi ((Θ_condensed r).app S) :=
begin
---- NOTE: this is the wrong approach, we need to reduce to finite `S`
--   refine condensed.epi_to_Condensed_map _ _ _ _,
  all_goals { sorry },
end

end theta

section ses

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p

open CompHausFiltPseuNormGrp₁

lemma exact_with_constant_profinite (S : Profinite) :
  ∃ C ≥ 1, exact_with_constant ((Φ_profinite_rescaled r).app S) ((Θ_profinite p).app S) C :=
begin
  refine ⟨sorry, sorry, _⟩,
  refine exact_with_constant_extend _ _ _ _ _,
  sorry,
end

lemma exact (S : Profinite) : exact ((Φ_condensed_rescaled r).app S) ((Θ_condensed p).app S) :=
begin
  obtain ⟨C, hC, H⟩ := exact_with_constant_profinite p S,
  exact condensed.exact_of_exact_with_constant _ _ C hC H,
end

end ses

end laurent_measures
