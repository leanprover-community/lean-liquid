import pseudo_normed_group.basic

local attribute [instance] type_pow

open_locale nnreal big_operators

namespace pseudo_normed_group

section splittable

class splittable (M : Type*) [pseudo_normed_group M] (N : ℕ) (d : ℝ≥0) :=
(exists_sum : ∀ (c : ℝ≥0) (x : M) (hx : x ∈ filtration M c),
  ∃ y : fin N → M, (x = ∑ i, y i) ∧ (∀ i, y i ∈ filtration M (c/N + d)))

variables {M : Type*} [pseudo_normed_group M] (N : ℕ) (d : ℝ≥0) [splittable M N d]

lemma exists_sum (c : ℝ≥0) (x : M) (hx : x ∈ filtration M c) :
  ∃ y : fin N → M, (x = ∑ i, y i) ∧ (y ∈ filtration (M^N) (c/N + d)) :=
splittable.exists_sum c x hx

instance splittable_pi {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)]
  (N : ℕ) (d : ℝ≥0) [∀ i, splittable (M i) N d] :
  splittable (Π i, M i) N d :=
{ exists_sum := λ c x hx,
  begin
    have := λ i, exists_sum N d c (x i) (hx i),
    choose y hy1 hy2 using this,
    refine ⟨function.swap y, _, function.swap hy2⟩,
    ext i, rw [hy1], symmetry, convert finset.sum_apply i _ _,
  end }

end splittable

end pseudo_normed_group
