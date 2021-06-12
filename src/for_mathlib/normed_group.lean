import topology.algebra.normed_group
import topology.sequences

open_locale big_operators topological_space uniformity
open finset filter

variables {G : Type*} [semi_normed_group G]
          {H : Type*} [semi_normed_group H]

universe u


lemma controlled_sum_of_mem_closure {s : add_subgroup G} {g : G}
  (hg : g ∈ closure (s : set G)) {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ v : ℕ → G, tendsto (λ n, ∑ i in range (n+1), v i) at_top (𝓝 g) ∧
               (∀ n, v n ∈ s) ∧
               ∥v 0 - g∥ < b 0 ∧ ∀ n > 0, ∥v n∥ < b n :=
begin
  obtain ⟨u : ℕ → G, u_in : ∀ n, u n ∈ s, lim_u : tendsto u at_top (𝓝 g)⟩ :=
    mem_closure_iff_seq_limit.mp hg,
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ∥u n - g∥ < b 0,
  { have : {x | ∥x - g∥ < b 0} ∈ 𝓝 g,
    { simp_rw ← dist_eq_norm,
      exact metric.ball_mem_nhds _ (b_pos _) },
    exact tendsto_at_top'.mp lim_u _ this },
  set z : ℕ → G := λ n, u (n + n₀),
  have lim_z : tendsto z at_top (𝓝 g) := lim_u.comp (tendsto_add_at_top_nat n₀),
  have mem_𝓤 : ∀ n, {p : G × G | ∥p.1 - p.2∥ < b (n + 1)} ∈ 𝓤 G :=
  λ n, by simpa [← dist_eq_norm] using metric.dist_mem_uniformity (b_pos $ n+1),
  obtain ⟨φ : ℕ → ℕ, φ_extr : strict_mono φ,
          hφ : ∀ n, ∥z (φ $ n + 1) - z (φ n)∥ < b (n + 1)⟩ :=
    lim_z.cauchy_seq.subseq_mem mem_𝓤,
  set w : ℕ → G := z ∘ φ,
  have hw : tendsto w at_top (𝓝 g),
    from lim_z.comp (strict_mono_tendsto_at_top φ_extr),
  -- *TODO* in mathlib, move strict_mono_tendsto_at_top into the strict_mono namespace
  set v : ℕ → G := λ i, if i = 0 then w 0 else w i - w (i - 1),
  refine ⟨v, tendsto.congr (finset.eq_sum_range_sub' w) hw , _,
          hn₀ _ (n₀.le_add_left _), _⟩,
  { rintro ⟨⟩,
    { change w 0 ∈ s,
      apply u_in },
    { apply s.sub_mem ; apply u_in }, },
  { intros l hl,
    obtain ⟨k, rfl⟩ : ∃ k, l = k+1, exact nat.exists_eq_succ_of_ne_zero (ne_of_gt hl),
    apply hφ },
end

lemma controlled_sum_of_mem_closure_range {j : G →+ H} {h : H}
  (Hh : h ∈ (closure $ (j.range : set H))) {b : ℕ → ℝ}
  (b_pos : ∀ n, 0 < b n) :
  ∃ g : ℕ → G, tendsto (λ n, ∑ i in range (n+1), j (g i)) at_top (𝓝 h) ∧
               ∥j (g 0) - h∥ < b 0 ∧ ∀ n > 0, ∥j (g n)∥ < b n :=
begin
  rcases controlled_sum_of_mem_closure Hh b_pos with ⟨v, sum_v, v_in, hv₀, hv_pos⟩,
  choose g hg using v_in,
  change ∀ (n : ℕ), j (g n) = v n at hg,
  refine ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀, λ n hn,
          by simpa [hg] using hv_pos n hn⟩
end
