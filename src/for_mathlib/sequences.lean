import topology.sequences
import topology.algebra.normed_group
import topology.algebra.group_completion
import topology.metric_space.completion

import for_mathlib.normed_group_hom

-- **TODO** Move completion.normed_group out of for_mathlib.locally_constant

noncomputable theory

open filter set function
open_locale uniformity filter topological_space

variables {X : Type*}

-- The next three lemmas could have more descriptive names...

lemma yo {P : ℕ → ℕ → Prop} (h : ∀ n, ∀ N, ∃ k > N, P n k) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
begin
  choose u hu hu' using h,
  use (λ n, nat.rec_on n (u 0 0) (λ n v, u (n+1) v) : ℕ → ℕ),
  split,
  { apply strict_mono.nat,
    intro n,
    apply hu },
  { intros n,
    cases n ; simp [hu'] },
end

lemma yo' {P : ℕ → ℕ → Prop} (h : ∀ n, ∀ N, ∃ k ≥ N, P n k) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
begin
  apply yo,
  intros n N,
  rcases h n (N+1) with ⟨k, hk, hk'⟩,
  use k; tauto
end

lemma yo'' {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ N, ∀ k ≥ N, P n k) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
begin
  apply yo',
  intros n N,
  cases h n with N₀ hN₀,
  exact ⟨max N N₀, le_max_left _ _, hN₀ _ $ le_max_right _ _⟩,
end


/-
The next four lemmas turned out to be useless here, but could be put in mathlib anyway

lemma e {F : filter X} {V : ℕ → set X} (hV : ∀ n, V n ∈ F) {u : ℕ → X} (hu : tendsto u at_top F) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, u (φ n) ∈ V n :=
yo'' (λ n, tendsto_at_top'.mp hu _ (hV n) : ∀ n, ∃ N, ∀ k ≥ N, u k ∈ V n)

lemma tendsto_at_top_diagonal {α : Type*} [semilattice_sup α] : tendsto (λ a : α, (a, a)) at_top at_top :=
by { rw ← prod_at_top_at_top_eq, exact tendsto_id.prod_mk tendsto_id }

lemma filter.tendsto.prod_map_prod_at_top {α β γ : Type*} [semilattice_sup γ] {F : filter α} {G : filter β}
  {f : α → γ} {g : β → γ} (hf : tendsto f F at_top) (hg : tendsto g G at_top) :
  tendsto (prod.map f g) (F ×ᶠ G)  at_top :=
by { rw ← prod_at_top_at_top_eq, exact hf.prod_map hg, }

lemma filter.tendsto.prod_at_top {α γ : Type*} [semilattice_sup α] [semilattice_sup γ]
  {f g : α → γ} (hf : tendsto f at_top at_top) (hg : tendsto g at_top at_top) :
  tendsto (prod.map f g) at_top  at_top :=
by { rw ← prod_at_top_at_top_eq, exact hf.prod_map_prod_at_top hg, }

lemma one {X : Type*} [uniform_space X] {V : ℕ → set (X × X)} (hV : ∀ n, V n ∈ 𝓤 X) {u : ℕ → X}
  (hu : cauchy_seq u)
  {f g : ℕ → ℕ} (hf : tendsto f at_top at_top) (hg : tendsto g at_top at_top)
  : ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) ∈ V n :=
begin
  rw cauchy_seq_iff_tendsto at hu,
  exact e hV ((hu.comp $ hf.prod_at_top hg).comp tendsto_at_top_diagonal),
end  -/

lemma cauchy_seq_iff {X : Type*} [uniform_space X] {u : ℕ → X} :
cauchy_seq u ↔ ∀ V ∈ 𝓤 X, ∃ N, ∀ k ≥ N, ∀ l ≥ N, (u l, u k) ∈ V :=
begin
  rw [cauchy_seq_iff_tendsto, tendsto_at_top'],
  apply forall_congr, intro V, apply forall_congr, intro V_in,
  split,
  { rintros ⟨⟨k, l⟩, H⟩,
    exact ⟨max k l, λ n hn m hm, H (m, n) ⟨le_of_max_le_left hm, le_of_max_le_right hn⟩⟩ },
  { rintros ⟨N, hN⟩,
    exact ⟨(N, N), λ ⟨k, l⟩ ⟨hk, hl⟩, hN _ hl _ hk⟩ },
end

-- **FIXME** Better name...
lemma foo {X : Type*} [uniform_space X] {V : ℕ → set (X × X)} (hV : ∀ n, V n ∈ 𝓤 X) {u : ℕ → X}
  (hu : cauchy_seq u) : ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, (u $ φ (n + 1), u $ φ n) ∈ V n :=
begin
  have : ∀ n, ∃ N, ∀ k ≥ N, ∀ l ≥ k, (u l, u k) ∈ V n,
  { intro n,
    rw [cauchy_seq_iff] at hu,
    rcases hu _ (hV n) with ⟨N, H⟩,
    exact ⟨N, λ k hk l hl, by apply H ; linarith⟩ },
  rcases yo'' this with ⟨φ, φ_extr, hφ⟩,
  dsimp at hφ,
  refine ⟨φ, φ_extr, _⟩,
  intro n,
  apply hφ,
  exact (φ_extr (lt_add_one n)).le,
end

open_locale big_operators
open finset (range)

lemma finset.eq_sum_range_sub {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  f n = f 0 + ∑ i in range n, (f (i+1) - f i) :=
by { rw finset.sum_range_sub, abel }

lemma finset.eq_sum_range_sub' {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  f n = ∑ i in range (n + 1), if i = 0 then f 0 else f i - f (i - 1) :=
begin
  conv_lhs { rw [finset.eq_sum_range_sub f] },
  simp [finset.sum_range_succ', add_comm]
end

variables {G : Type*} [normed_group G]
          {H : Type*} [normed_group H]

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
   foo mem_𝓤 lim_z.cauchy_seq,
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
open uniform_space

def j : G →+ completion G :=
⟨(coe : G → completion G), is_add_group_hom.map_zero coe, is_add_hom.map_add coe⟩

lemma j_dense : dense ((j : G →+ completion G).range : set $ completion G):=
completion.dense_range_coe

lemma completion.controlled_sum (h : completion G)
  {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ g : ℕ → G, tendsto (λ n, ∑ i in range (n+1), j (g i)) at_top (𝓝 h) ∧
               ∥j (g 0) - h∥ < b 0 ∧ ∀ n > 0, ∥g n∥ < b n :=
let ⟨g, sum_g, hg₀, H⟩ := controlled_sum_of_mem_closure_range (j_dense h) b_pos in
⟨g, sum_g, hg₀, by simpa [j] using H⟩
