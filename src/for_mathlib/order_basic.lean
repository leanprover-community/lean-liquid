import order.filter.at_top_bot

open filter
-- To be PRed to order.basic

lemma strict_mono_forall_of_frequently {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ᶠ k in at_top, P n k) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
begin
  simp only [frequently_at_top'] at h,
  choose u hu hu' using h,
  use (λ n, nat.rec_on n (u 0 0) (λ n v, u (n+1) v) : ℕ → ℕ),
  split,
  { apply strict_mono.nat,
    intro n,
    apply hu },
  { intros n,
    cases n ; simp [hu'] },
end

lemma strict_mono_forall_of_eventually  {P : ℕ → ℕ → Prop} (h : ∀ n, ∀ᶠ k in at_top, P n k) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
strict_mono_forall_of_frequently (λ n, (h n).frequently)

lemma strict_mono_forall_of_eventually' {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ N, ∀ k ≥ N, P n k) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
strict_mono_forall_of_eventually (by simp [eventually_at_top, h])
