import for_mathlib.Profinite.extend
import for_mathlib.split_exact

import condensed.ab

.

universe u

open_locale nnreal

open category_theory opposite pseudo_normed_group

namespace CompHausFiltPseuNormGrp₁

variables {A B C : CompHausFiltPseuNormGrp₁.{u}}

structure exact_with_constants (f : A ⟶ B) (g : B ⟶ C) (Cf Cg : ℝ≥0) : Prop :=
[mono : mono f]
[epi : epi g]
-- [exact : exact f g] -- need exactness in `Ab`
(cond : ∀ c : ℝ≥0,
  g ⁻¹' {0} ∩ (filtration B c) ⊂ f '' (filtration A (Cf * c)) ∧
  filtration C c ⊆ g '' (filtration B (Cg * c)))

lemma exact_with_constants_extend {A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (Cf Cg : ℝ≥0)
  (hfg : ∀ S, exact_with_constants (f.app S) (g.app S) Cf Cg) (S : Profinite) :
  exact_with_constants
   ((Profinite.extend_nat_trans f).app S) ((Profinite.extend_nat_trans g).app S) Cf Cg :=
sorry

end CompHausFiltPseuNormGrp₁

namespace condensed

open CompHausFiltPseuNormGrp₁

lemma exact_iff_ExtrDisc  {A B C : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ ∀ (S : ExtrDisc),
    exact (f.1.app $ ExtrDisc_to_Profinite.op.obj (op S))
          (g.1.app $ ExtrDisc_to_Profinite.op.obj (op S)) :=
sorry

lemma exact_of_exact_with_constants {A B C : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (Cf Cg : ℝ≥0)
  (hfg : exact_with_constants f g Cf Cg) :
  exact (to_Condensed.map f) (to_Condensed.map g) :=
begin
  rw exact_iff_ExtrDisc,
  intro S,
  simp only [subtype.val_eq_coe, CompHausFiltPseuNormGrp.presheaf.map_apply, to_Condensed_map,
    whisker_right_app, CompHausFiltPseuNormGrp.Presheaf.map_app, Ab.exact_ulift_map],
  sorry
end

end condensed
