import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

structure add_subgroup.is_kernel {M N : Type*} [semi_normed_group M] [semi_normed_group N]
  (f : normed_group_hom M N) : Prop :=
(injective : function.injective f)
(norm : ∀ x, ∥f x∥ = ∥x∥)

def system_of_complexes.is_kernel {M M' : system_of_complexes} (f : M ⟶ M') : Prop :=
∀ c i, add_subgroup.is_kernel (f.apply : M c i ⟶ M' c i)

variables (M M' N : system_of_complexes.{u}) (f : N ⟶ M) (g : M ⟶ M')

lemma weak_normed_snake_dual {k k' k'' K K' K'' r₁ r₂ : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')] [hk'' : fact (1 ≤ k'')]
  {m : ℕ} {c₀ : ℝ≥0}
  (hM : M.is_weak_bounded_exact k K (m+1) c₀)
  (hM' : M'.is_weak_bounded_exact k' K' (m+1) c₀)
  (hM'_adm : M'.admissible)
  (hg : ∀ c i (x : M (k'' * c) i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ m+1+1) (y : M' (k'' * c) i),
    ∃ (x : M (k'' * c) i), g x = y ∧ ∥x∥ ≤ r₂ * ∥x∥)
  (hg : ∀ c i, (f.apply : N c i ⟶ M c i).range = g.apply.ker)
  (hgker : system_of_complexes.is_kernel f) :
  N.is_weak_bounded_exact (k''*k*k') (K'*(K*K'' + 1)) m c₀ := sorry
