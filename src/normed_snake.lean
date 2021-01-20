import system_of_complexes

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite

section prereqs -- move this
variables {V W : Type*} [normed_group V] [normed_group W]

def normed_group_hom.is_strict (f : normed_group_hom V W) : Prop :=
∀ v, ∥f v∥ = ∥v∥

lemma normed_group_hom.is_strict.injective {f : normed_group_hom V W} (hf : f.is_strict) :
  function.injective f :=
sorry

end prereqs

variables {M M' N : system_of_complexes.{u}} (f : M ⟶ M') (g : M' ⟶ N)

def category_theory.has_hom.hom.apply (f : M ⟶ N) (c : ℝ≥0) (i : ℤ) :=
(f.app (op c)).f i

variables (M M' N)

/-- The normed snake lemma. See Proposition -/
lemma normed_snake (k : ℝ≥0) (m : ℤ) (c₀ : ℝ≥0) [fact (1 ≤ k)]
  (hf : ∀ c i, normed_group_hom.is_strict (f.apply c i))
  (Hf : ∀ (c : ℝ≥0) (i : ℤ) (hi : i ≤ m+1) (x : M.X (k * c) i),
    ∥(M.res x : M.X c i)∥ ≤ k * ∥f.apply (k*c) i x∥)
  (hg : ∀ c i, function.surjective (g.apply c i))
  (hN : ∀ c i x, ∥g.apply c i x∥ = ∥x∥)
  -- jmc: Is this ↑↑ the correct way of saying "`N` has the quotient norm"?
  (hM : M.is_bdd_exact_for_bdd_degree_above_idx k m c₀)
  (hM' : M'.is_bdd_exact_for_bdd_degree_above_idx k m c₀)
  (hM_adm : M.admissible)
  (hM'_adm : M'.admissible)
  (k_new : ℝ≥0) [fact (1 ≤ k_new)] (hk : k_new = k^3 + k) :
  N.is_bdd_exact_for_bdd_degree_above_idx k_new m c₀ :=
sorry
