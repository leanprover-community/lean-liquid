import pseudo_normed_group.splittable
import pseudo_normed_group.finsupp

local attribute [instance] type_pow

open_locale nnreal big_operators

namespace pseudo_normed_group

class strongly_splittable (M : Type*) [pseudo_normed_group M] (N : ℕ) (d : ℝ≥0) : Prop :=
(exists_strong_split' : ∀ (c : ℝ≥0) (x : M) (hx : x ∈ filtration M c),
  ∃ (y : fin N → M) (γ : fin N → ℝ≥0), (x = ∑ i, y i) ∧ (∀ i, y i ∈ filtration M (γ i)) ∧
    (∑ i, γ i ≤ c) ∧ (∀ i j, γ i ≤ γ j + d))

variables {M : Type*} [pseudo_normed_group M] (N : ℕ) (d : ℝ≥0) [strongly_splittable M N d]

lemma exists_strong_split (c : ℝ≥0) (x : M) (hx : x ∈ filtration M c) :
  ∃ (y : fin N → M) (γ : fin N → ℝ≥0), (x = ∑ i, y i) ∧ (∀ i, y i ∈ filtration M (γ i)) ∧
    (∑ i, γ i ≤ c) ∧ (∀ i j, γ i ≤ γ j + d) :=
strongly_splittable.exists_strong_split' c x hx

namespace strongly_splittable

instance [hN : fact (0 < N)] : splittable M N d :=
begin
  constructor,
  intros c x hx,
  obtain ⟨y, γ, h₁, h₂, h₃, h₄⟩ := exists_strong_split N d c x hx,
  refine ⟨y, h₁, λ i, filtration_mono _ (h₂ i)⟩,
  suffices : ∃ j, γ j ≤ c / N,
  { rcases this with ⟨j, hj⟩,
    calc γ i ≤ γ j + d   : h₄ i j
         ... ≤ c / N + d : add_le_add hj le_rfl, },
  by_contra' H : ∀ j, c / N < γ j,
  suffices : c < c, from lt_irrefl c this,
  calc c = ∑ j : fin N, c / N : _
     ... < ∑ j, γ j           : finset.sum_lt_sum (λ j _, (H j).le) ⟨i, finset.mem_univ _, H i⟩
     ... ≤ c                  : h₃,
  rw [finset.sum_const, finset.card_fin, nsmul_eq_mul, mul_div_cancel'],
  exact_mod_cast hN.out.ne'
end

instance {ι : Type*} : strongly_splittable (ι →₀ M) N d :=
begin
  constructor,
  rintro c x,
  obtain ⟨s, hs⟩ : ∃ s : finset ι, x.support ⊆ s, from ⟨x.support, by refl⟩,
  classical,
  induction s using finset.induction with i₀ s h₀ IH generalizing c x,
  { rintro -,
    rw [finset.subset_empty, finsupp.support_eq_empty] at hs, subst x,
    refine ⟨0, 0, by simp, λ i, zero_mem_filtration _, by simp⟩, },
  rintro ⟨γ, hγ, hx⟩,
  obtain ⟨y₀, γ₀, h₀₁, h₀₂, h₀₃, h₀₄⟩ := exists_strong_split N d (γ i₀) (x i₀) (hx i₀),
  let x₀ := finsupp.single i (x i),
  let xₛ := x.erase i,
  have h₀ₛ : x = x₀ + xₛ,
  { sorry },
  have hxs : xₛ.support ⊆ s,
  { sorry },
  -- Proof sketch:
  -- Use the induction hypothesis to obtain a strong split `yₛ` of `xₛ`, with pseudo-norms `γₛ`.
  -- Then reindex the `γ₀` to be increasing and the `γₛ` to be decreasing.
  -- After the corresponding reindexing of `y₀` and `yₛ`, define `y = y₀ + yₛ`.
  -- Now go with the flow.
  sorry
  -- Old stuff:
  -- have := (λ i, exists_strong_split N d (γ i) (x i) (hx i)),
  -- choose y δ H1 H2 H3 H4 using this,
end

-- jmc: not sure if this is true, but we shouldn't need it
-- instance strongly_splittable_pi {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)]
--   (N : ℕ) (d : ℝ≥0) [∀ i, strongly_splittable (M i) N d] :
--   strongly_splittable (Π i, M i) N d :=
-- { exists_strong_split := λ c x hx,
--   begin
--     have := λ i, exists_strong_split N d c (x i) (hx i),
--     choose y γ h1 h2 h3 using this,
--     refine ⟨function.swap y, function.swap γ, _, _, _⟩,
--     ext i, rw [hy1], symmetry, convert finset.sum_apply i _ _,
--   end }

end strongly_splittable

end pseudo_normed_group
