import .basic

noncomputable theory

namespace category_theory

namespace arrow

class split {C : Type*} [category C] (f : arrow C) :=
(σ : f.right ⟶ f.left)
(is_splitting' : σ ≫ f.hom = 𝟙 _ . obviously)

restate_axiom split.is_splitting'

attribute [simp] split.is_splitting

end arrow

namespace cech

variables {C : Type*} [category C]

open_locale simplicial

-- A splitting of the Cech nerve
def cech_splitting {X B : C} (f : X ⟶ B) (g : B ⟶ X) (splitting : g ≫ f = 𝟙 B)
  [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)]
  (n : ℕ) : (cech_obj f) _[n] ⟶ (cech_obj f) _[n+1] :=
limits.wide_pullback.lift limits.wide_pullback.base
(λ i, if hi : i = 0 then limits.wide_pullback.base ≫ g else limits.wide_pullback.π $ ufin.pred i hi) $
by {intros i, split_ifs, all_goals {simp [splitting]}}

end cech

end category_theory
