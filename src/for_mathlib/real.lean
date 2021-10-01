import analysis.convex.specific_functions
import analysis.convex.combination

open real set
open_locale big_operators

/-

variables {E F : Type*}
variables [ordered_add_comm_group E] [module ℝ E]
variables [ordered_add_comm_group F] [module ℝ F]
variables {s : set E} {f : E → F} (t : set F) (g : F → E)

lemma concave_on_of_convex_on_inverse (hs : convex ℝ s) (hg : convex_on t g)
  (hfs : s ⊆ f ⁻¹' t) (hgt : t ⊆ g ⁻¹' s)
  (hgf : ∀ {x}, x ∈ s → g (f x) = x) (hfg : ∀ {y}, y ∈ t → f (g y) = y)
  (hf : ∀ {x₁ x₂}, x₁ ∈ s → x₂ ∈ s → x₁ ≤ x₂ → f x₁ ≤ f x₂) :
  concave_on s f :=
begin
  refine ⟨hs, _⟩,
  intros x y xs ys a b ha hb hab,
  have H : a • f x + b • f y ∈ t := hg.1 (hfs xs) (hfs ys) ha hb hab,
  have := hf (hgt H) _ (hg.2 (hfs xs) (hfs ys) ha hb hab),
  { rwa [hgf xs, hgf ys, hfg H] at this },
  { rw [hgf xs, hgf ys], exact hs xs ys ha hb hab, }
end

lemma concave_on_rpow {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : concave_on (Ici 0) (λ x : ℝ, x^p) :=
begin
  by_cases hp : p = 0,
  { simpa only [hp, rpow_zero] using concave_on_const (1:ℝ) (convex_Ici 0) },
  have h0p : 0 < p := lt_of_le_of_ne hp0 (ne.symm hp),
  have : ∀ {s t : set ℝ}, s ⊆ t ↔ (∀ x, x ∈ s → x ∈ t) := λ s t, iff.rfl,
  apply concave_on_of_convex_on_inverse (Ici 0) (λ x:ℝ, x ^ (p⁻¹)) (convex_Ici 0)
    (convex_on_rpow (one_le_inv h0p hp1)),
  all_goals { simp only [this, mem_Ici, mem_preimage] },
  { intros x hx, exact rpow_nonneg_of_nonneg hx _ },
  { intros x hx, exact rpow_nonneg_of_nonneg hx _ },
  { intros x hx, rw [← rpow_mul hx, mul_inv_cancel hp, rpow_one], },
  { intros x hx, rw [← rpow_mul hx, inv_mul_cancel hp, rpow_one], },
  { intros, apply rpow_le_rpow, assumption' },
end

-/
