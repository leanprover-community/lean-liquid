import laurent_measures.ses
import laurent_measures.condensed
import real_measures.condensed
import condensed.condensify

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

end theta

section ses

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p

open CompHausFiltPseuNormGrp₁

theorem short_exact (S : Profinite) :
  short_exact ((condensify_Tinv2 _).app S) ((condensify_map $ Θ_fintype_nat_trans p).app S) :=
begin
  refine condensify_nonstrict_exact _ _ (r⁻¹ + 2) (Tinv2_bound_by _)
  -- C₂ bound
  (λ x, 37) -- warning: probably not right
  -- C₄ bound
  (λ x, 59) -- ditto
  -- proofs that f(x) ≥ x
  sorry sorry
    (λ S, injective_ϕ')
    (λ S, by { ext1 F, apply θ_ϕ_complex }) _ _ _,
  -- proof of some boundedness thing
  { clear S,
    -- change to unbundled language
    rintros S c' (f : laurent_measures r S) ⟨hf1,
      (hf2 : f ∈ pseudo_normed_group.filtration (laurent_measures r S) c')⟩,
    rw [set.mem_preimage, set.mem_singleton_iff] at hf1,
    rw set.mem_image,
    change ∃ x : laurent_measures r S,
      x ∈ pseudo_normed_group.filtration (laurent_measures r S) _ ∧ _,
    sorry },
  { clear S,
    rintros S c' f,

    sorry },
end

end ses

end laurent_measures
