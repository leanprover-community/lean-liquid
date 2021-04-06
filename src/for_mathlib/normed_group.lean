import topology.algebra.normed_group
import topology.sequences

import for_mathlib.uniform_space_cauchy
import for_mathlib.big_operators_basic

open_locale big_operators topological_space uniformity
open finset filter

variables {G : Type*} [semi_normed_group G]
          {H : Type*} [semi_normed_group H]

lemma norm_le_insert' (a b : G) : ∥a∥ ≤ ∥b∥ + ∥a - b∥ :=
begin
  rw norm_sub_rev,
  exact norm_le_insert b a
end

lemma normed_group.mem_closure_iff {s : set G} {x : G} : x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, ∥x - y∥ < ε :=
by simp [metric.mem_closure_iff, dist_eq_norm]

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



lemma normed_group.cauchy_seq_iff {u : ℕ → G} :
  cauchy_seq u ↔ ∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → ∥u m - u n∥ < ε :=
by simp [metric.cauchy_seq_iff, dist_eq_norm]

lemma cauchy_seq.add {u v : ℕ → G} (hu : cauchy_seq u) (hv : cauchy_seq v) : cauchy_seq (u + v) :=
begin
  rw normed_group.cauchy_seq_iff at *,
  intros ε ε_pos,
  rcases hu (ε/2) (half_pos ε_pos) with ⟨Nu, hNu⟩,
  rcases hv (ε/2) (half_pos ε_pos) with ⟨Nv, hNv⟩,
  use max Nu Nv,
  intros m n hm hn,
  replace hm := max_le_iff.mp hm,
  replace hn := max_le_iff.mp hn,

  calc ∥(u + v) m - (u + v) n∥ = ∥u m + v m - (u n + v n)∥ : rfl
  ... = ∥(u m - u n) + (v m - v n)∥ : by abel
  ... ≤ ∥u m - u n∥ + ∥v m - v n∥ : norm_add_le _ _
  ... < ε : by linarith [hNu m n hm.1 hn.1, hNv m n hm.2 hn.2]
end

lemma cauchy_seq_const (x : G) : cauchy_seq (λ n : ℕ, x) :=
tendsto.cauchy_seq tendsto_const_nhds


lemma eventually_constant_sum {G : Type*} [add_comm_monoid G] {u : ℕ → G} {N : ℕ}
  (hu : ∀ n ≥ N, u n = 0) {n : ℕ} (hn : n ≥ N) :
  ∑ k in range (n + 1), u k = ∑ k in range (N + 1), u k :=
begin
  obtain ⟨m, rfl : n = N + m⟩ := le_iff_exists_add.mp hn,
  clear hn,
  induction m with m hm,
  { simp },
  erw [sum_range_succ, hm],
  simp [hu]
end

lemma cauchy_seq_of_eventually_eq {u v : ℕ → G} {N : ℕ} (huv : ∀ n ≥ N, u n = v n)
  (hv : cauchy_seq (λ n, ∑ k in range (n+1), v k)) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  have : (λ n, ∑ k in range (n + 1), u k) = (λ n, ∑ k in range (n + 1), (u k - v k)) + (λ n, ∑ k in range (n + 1), v k),
  { ext n,
    simp },
  rw this, clear this,
  apply cauchy_seq.add _ hv,
  apply tendsto.cauchy_seq,
  have : ∀ n ≥ N, ∑ (k : ℕ) in range (n + 1), (u k - v k) = ∑ (k : ℕ) in range (N + 1), (u k - v k),
  { intros n hn,
    rw eventually_constant_sum _ hn,
    intros m hm,
    simp [huv m hm] },
  apply tendsto.congr',
  apply eventually_eq.symm,
  change ∀ᶠ n in at_top, _,
  rw eventually_at_top,
  use N,
  exact this,
  exact tendsto_const_nhds
end
