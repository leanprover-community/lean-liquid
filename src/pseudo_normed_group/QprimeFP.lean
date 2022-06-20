import pseudo_normed_group.FP2
import condensed.adjunctions
import free_pfpng.acyclic
import for_mathlib.derived.ext_coproducts
import for_mathlib.derived.example
import breen_deligne.eval2
import system_of_complexes.shift_sub_id

noncomputable theory

open_locale nnreal

universe u

open category_theory category_theory.limits breen_deligne

section step1

variables (r' : ℝ≥0)
variables (BD : breen_deligne.data) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

abbreviation freeCond := Profinite_to_Condensed.{u} ⋙ CondensedSet_to_Condensed_Ab

def QprimeFP_nat : ℝ≥0 ⥤ chain_complex (Condensed.{u} Ab.{u+1}) ℕ :=
FPsystem r' BD ⟨M⟩ κ ⋙ (freeCond.{u}.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _

def QprimeFP_int : ℝ≥0 ⥤ cochain_complex (Condensed.{u} Ab.{u+1}) ℤ :=
QprimeFP_nat r' BD κ M ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up

def QprimeFP : ℝ≥0 ⥤ bounded_homotopy_category (Condensed.{u} Ab.{u+1}) :=
QprimeFP_nat r' BD κ M ⋙ chain_complex.to_bounded_homotopy_category

end step1

section step2

variables {r' : ℝ≥0}
variables (BD : breen_deligne.package) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

abbreviation freeCond' := Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab

def ProFiltPseuNormGrpWithTinv₁.to_Condensed : Condensed.{u} Ab.{u+1} :=
(PFPNGT₁_to_CHFPNG₁ₑₗ r' ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u} ⋙
  CompHausFiltPseuNormGrp.to_Condensed.{u}).obj M

def QprimeFP_incl (c : ℝ≥0) :
  (QprimeFP_int r' BD.data κ M).obj c ⟶
  (BD.eval' freeCond').obj M.to_Condensed :=
(homological_complex.embed complex_shape.embedding.nat_down_int_up).map
{ f := λ n, CondensedSet_to_Condensed_Ab.map sorry,
  comm' := sorry }

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

def QprimeFP_sigma_proj :
  ∐ (λ k, (QprimeFP_int r' BD.data κ M).obj (ι k)) ⟶
  (BD.eval' freeCond').obj M.to_Condensed :=
sigma.desc $ λ n, QprimeFP_incl BD κ M _

instance QprimeFP.uniformly_bounded :
  bounded_homotopy_category.uniformly_bounded (λ k, (QprimeFP r' BD.data κ M).obj (ι k)) :=
begin
  use 1, intro k, apply chain_complex.bounded_by_one,
end

end step2

section step3
open bounded_homotopy_category

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)
variables (A : ℝ≥0 ⥤ cochain_complex (Condensed.{u} Ab.{u+1}) ℤ)
-- variables [uniformly_bounded (λ k, A.obj (ι k))]

def sigma_shift : ∐ (λ k, A.obj (ι k)) ⟶ ∐ (λ k, A.obj (ι k)) :=
sigma.desc $ λ k, A.map (hom_of_le $ hι $ by { cases k, recover, swap, exact ⟨k.down + 1⟩, apply nat.le_succ }) ≫
  sigma.ι (λ k, A.obj (ι k)) ⟨k.down + 1⟩

end step3

section step4

variables {r' : ℝ≥0}
variables (BD : breen_deligne.package) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

lemma QprimeFP.short_exact (n : ℤ) :
  short_exact ((sigma_shift _ hι _).f n) ((QprimeFP_sigma_proj BD κ M ι).f n) :=
sorry

end step4

section step5

variables {r' : ℝ≥0}
variables (BD : breen_deligne.data)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

def QprimeFP.Tinv [∀ c n, fact (κ c n ≤ r' * κ₂ c n)] :
  (QprimeFP r' BD κ M) ⟶ (QprimeFP r' BD κ₂ M) :=
sorry

/-- The natural inclusion map -/
def QprimeFP.ι [∀ c n, fact (κ c n ≤ κ₂ c n)] :
  (QprimeFP r' BD κ M) ⟶ (QprimeFP r' BD κ₂ M) :=
sorry

end step5

-- variables (f : ℕ → ℝ≥0)
-- #check ∐ (λ i, (QprimeFP r' BD κ M).obj (f i))
