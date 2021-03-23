import tactic
import topology.uniform_space.cauchy
import for_mathlib.filter_at_top_bot

open filter
open_locale uniformity

lemma cauchy_seq.subseq_subseq_mem {X : Type*} [uniform_space X] {V : ℕ → set (X × X)} (hV : ∀ n, V n ∈ 𝓤 X) {u : ℕ → X}
  (hu : cauchy_seq u)
  {f g : ℕ → ℕ} (hf : tendsto f at_top at_top) (hg : tendsto g at_top at_top)
  : ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) ∈ V n :=
begin
  rw cauchy_seq_iff_tendsto at hu,
  exact ((hu.comp $ hf.prod_at_top hg).comp tendsto_at_top_diagonal).subseq_mem hV,
end

lemma cauchy_seq_iff' {X : Type*} [uniform_space X] {u : ℕ → X} :
cauchy_seq u ↔ ∀ V ∈ 𝓤 X, ∀ᶠ k in at_top, k ∈ (prod.map u u) ⁻¹' V :=
by simpa only [cauchy_seq_iff_tendsto]

lemma cauchy_seq_iff {X : Type*} [uniform_space X] {u : ℕ → X} :
cauchy_seq u ↔ ∀ V ∈ 𝓤 X, ∃ N, ∀ k ≥ N, ∀ l ≥ N, (u k, u l) ∈ V :=
by simp [cauchy_seq_iff', filter.eventually_at_top_prod_self', prod_map]

lemma cauchy_seq.subseq_mem {X : Type*} [uniform_space X] {V : ℕ → set (X × X)}
  (hV : ∀ n, V n ∈ 𝓤 X) {u : ℕ → X} (hu : cauchy_seq u) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, (u $ φ (n + 1), u $ φ n) ∈ V n :=
begin
  have : ∀ n, ∃ N, ∀ k ≥ N, ∀ l ≥ k, (u l, u k) ∈ V n,
  { intro n,
    rw [cauchy_seq_iff] at hu,
    rcases hu _ (hV n) with ⟨N, H⟩,
    exact ⟨N, λ k hk l hl, by apply H ; linarith⟩ },
  obtain ⟨φ : ℕ → ℕ, φ_extr : strict_mono φ, hφ : ∀ n, ∀ l ≥ φ n, (u l, u $ φ n) ∈ V n⟩ :=
    strict_mono_forall_of_eventually' this,
  exact ⟨φ, φ_extr, λ n, hφ _ _ (φ_extr $lt_add_one n).le⟩,
end
