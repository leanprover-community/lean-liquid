import for_mathlib.Profinite.extend
import condensed.ab

.

universe u

open_locale nnreal

open category_theory pseudo_normed_group

namespace CompHausFiltPseuNormGrp₁

variables {A B C : CompHausFiltPseuNormGrp₁.{u}}

def exact_with_constants (f : A ⟶ B) (g : B ⟶ C) (Cf Cg : ℝ≥0) : Prop :=
∀ c : ℝ≥0,
  g ⁻¹' {0} ∩ (filtration B c) ⊂ f '' (filtration A (Cf * c)) ∧
  filtration C c ⊆ g '' (filtration B (Cg * c))

lemma exact_with_constants_extend {A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (Cf Cg : ℝ≥0)
  (hfg : ∀ S, exact_with_constants (f.app S) (g.app S) Cf Cg) (S : Profinite) :
  exact_with_constants
   ((Profinite.extend_nat_trans f).app S) ((Profinite.extend_nat_trans g).app S) Cf Cg :=
sorry

end CompHausFiltPseuNormGrp₁

namespace condensed

open CompHausFiltPseuNormGrp₁

variables {A B C : CompHausFiltPseuNormGrp₁.{u}}

lemma exact_of_exact_with_constants (f : A ⟶ B) (g : B ⟶ C) (Cf Cg : ℝ≥0)
  (hfg : exact_with_constants f g Cf Cg) :
  exact (to_Condensed.map f) (to_Condensed.map g) :=
sorry

end condensed
