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
  let k_new := k^3 + k,
  suffices : ∃ (y : N.X c i), ∀ ε : ℝ, 0 < ε → ∥ N.res n - N.d y ∥ ≤ k_new * (∥ N.d n ∥ + ε),
  { rcases this with ⟨y, hy⟩,
    use y,
    apply le_of_forall_pos_le_add,
    intros ε hε,
    convert hy (ε / k_new) _,
    simp only [mul_add, add_right_inj],
    suffices : (k_new : ℝ) ≠ 0, by {field_simp only [this], ring},
    { refine ne_of_gt (lt_of_lt_of_le zero_lt_one _),
      change fact (1 ≤ k^3 + k),
      apply_instance },
    refine div_pos hε (lt_of_lt_of_le zero_lt_one _),
    change fact (1 ≤ k^3 + k),
    apply_instance },
  let n₁ := N.d n,
  obtain ⟨m', hm'⟩ := hgsur (k_new * c) (i + 1) n,
  let m₁' := M'.d m',
  let C := ∥n₁∥,
  sorry
end
