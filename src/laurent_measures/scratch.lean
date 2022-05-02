import laurent_measures.ses
import laurent_measures.condensed
import real_measures.condensed
import condensed.condensify
import laurent_measures.prop72 -- kmb's attempt to tidy up the analysis argument

universe u

noncomputable theory

open category_theory

open_locale nnreal

namespace laurent_measures

open laurent_measures_ses ProFiltPseuNormGrpWithTinv₁

section theta

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p

/-- If `0 < (p : ℝ≥0) < 1` and `S : Fintype` then Θ p S-/
def Θ (S : Fintype.{u}) :
  (Fintype_LaurentMeasures.{u} r ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r).obj S ⟶
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
  (Fintype_LaurentMeasures.{u} r ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r) ⟶ (real_measures.functor.{u} p) :=
{ app := λ S, Θ p S,
  naturality' := λ S T f, by { ext x t, apply θ_natural, } }
.

end theta

open_locale big_operators -- lol needs to be done before local notation

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p

open CompHausFiltPseuNormGrp₁
example (S : Fintype) (c' : ℝ≥0)
  ⦃f : real_measures p S⦄
  (hf : ∥f∥₊ ≤ c') :
  ∥({to_fun := λ (s : ↥S), psi_aux_lemma2.eval_half_inv (f s),
         summable' := sorry} : laurent_measures r S)∥₊ ≤
      max (c' * 2 * (1 - r)⁻¹) c' ∧
    (λ (s : ↥S),
         ∑' (n : ℤ),
           (psi_aux_lemma2.eval_half_inv (f s) n : ℝ) * 2⁻¹ ^ n) =
      f :=
begin
  change ∑ (s : S), _ ≤ c' at hf,
  refine ⟨(_ : ∑ (s : S), ∑' (n : ℤ), ((_) * _: ℝ≥0) ≤ _), sorry⟩,
  admit,
end

end laurent_measures
