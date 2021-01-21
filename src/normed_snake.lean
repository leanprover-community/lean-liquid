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
begin
  intros x y h,
  rw ← sub_eq_zero at *,
  suffices : ∥ x - y ∥ = 0, by simpa,
  rw ← hf,
  simpa,
end

end prereqs

variables {M M' N : system_of_complexes.{u}} (f : M ⟶ M') (g : M' ⟶ N)

def category_theory.has_hom.hom.apply (f : M ⟶ N) (c : ℝ≥0) (i : ℤ) :=
(f.app (op c)).f i

variables (M M' N)

/-- The normed snake lemma. See Proposition 9.10 from Analytic.pdf -/
lemma normed_snake (k : ℝ≥0) (m : ℤ) (c₀ : ℝ≥0) [fact (1 ≤ k)]
  (hf : ∀ c i, normed_group_hom.is_strict (f.apply c i))
  (Hf : ∀ (c : ℝ≥0) (i : ℤ) (hi : i ≤ m+1) (x : M.X (k * c) i),
    ∥(M.res x : M.X c i)∥ ≤ k * ∥f.apply (k*c) i x∥)
  (hg : ∀ c i, (g.apply c i).ker = (f.apply c i).range)
  (hgsur : ∀ c i, function.surjective (g.apply c i))
  (hN : ∀ c i x, ∥g.apply c i x∥ = Inf {r : ℝ | ∃ y ∈ (f.apply c i).range, r = ∥x + y∥ })
  (hM : M.is_bdd_exact_for_bdd_degree_above_idx k m c₀)
  (hM' : M'.is_bdd_exact_for_bdd_degree_above_idx k m c₀)
  (hM_adm : M.admissible)
  (hM'_adm : M'.admissible) :
  N.is_bdd_exact_for_bdd_degree_above_idx (k^3 + k) (m-1) c₀ :=
begin
  intros c hc i hi n,
  set k_new := k^3 + k with hknew,
  suffices : ∃ (y : N.X c i), ∀ ε : ℝ, 0 < ε → ∥ N.res n - N.d y ∥ ≤ (k_new + ε) * ∥ N.d n ∥,
  { rcases this with ⟨y, hy⟩,
    use y,
    have : ↑k_new * ∥ N.d n ∥ = Inf { r | ∃ (ε : ℝ) (hε : 0 < ε), r = (k_new + ε) * ∥ N.d n ∥},
    { refine le_antisymm _ _,
      { rw real.le_Inf,
        { rintros z ⟨ε,hε,rfl⟩,
          simp only [le_add_iff_nonneg_right, add_mul],
          exact mul_nonneg (le_of_lt hε) (by simp) },
        { use (k_new + 1) * ∥ N.d n ∥,
          refine ⟨1, zero_lt_one, rfl⟩ },
        { use k_new * ∥ N.d n ∥,
          rintro y ⟨ε,hε,rfl⟩,
          simp only [le_add_iff_nonneg_right, add_mul],
          exact mul_nonneg (le_of_lt hε) (by simp) } },
      { by_cases ∥ N.d n ∥ ≤ 0,
        { simp at h,
          simp only [h, norm_zero, exists_and_distrib_right, mul_zero],
          have : {r : ℝ | ∃ (ε : ℝ) (hε : 0 < ε), r = 0 } = {0},
          { ext t,
            refine ⟨λ ⟨r,hr,h⟩, h, λ ht, ⟨1,zero_lt_one, ht⟩⟩ },
          rw this,
          simp },
        apply le_of_forall_pos_le_add,
        intros ε hε,
        apply real.Inf_le,
        { use k_new * ∥ N.d n ∥,
          rintro y ⟨ε,hε,rfl⟩,
          simp only [le_add_iff_nonneg_right, add_mul],
          exact mul_nonneg (le_of_lt hε) (by simp) },
        { use ε / ∥ N.d n ∥,
          simp at h,
          split,
          apply div_pos hε,
          rwa norm_pos_iff,
          simp [add_mul],
          field_simp [h] } } },
    rw this,
    rw real.le_Inf,
    { rintros r ⟨ε,hε,rfl⟩,
      exact hy _ hε },
    { use (k_new + 1) * ∥ N.d n ∥,
      refine ⟨1, zero_lt_one, rfl⟩ },
    { use k_new * ∥ N.d n ∥,
      rintros y ⟨ε,hε,rfl⟩,
      simp only [le_add_iff_nonneg_right, add_mul],
      exact mul_nonneg (le_of_lt hε) (by simp) } },
  let n₁ := N.d n,
  obtain ⟨m', hm'⟩ := hgsur (k_new * c) (i + 1) n,
  let m₁' := M'.d m',
  let C := ∥n₁∥,
  sorry
end
