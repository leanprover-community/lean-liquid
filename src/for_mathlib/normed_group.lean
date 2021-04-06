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

section PR7066
noncomputable theory

namespace metric

open set filter uniform_space uniform_space.completion
open_locale filter

variables {α : Type*} [pseudo_metric_space α]

/-- The distance on the completion is obtained by extending the distance on the original space,
by uniform continuity. -/
instance foo : has_dist (completion α) :=
⟨completion.extension₂ dist⟩

/-- The new distance is uniformly continuous. -/
protected lemma completion.uniform_continuous_dist' :
  uniform_continuous (λp:completion α × completion α, dist p.1 p.2) :=
uniform_continuous_extension₂ dist

/-- The new distance is an extension of the original distance. -/
protected lemma completion.dist_eq' (x y : α) : dist (x : completion α) y = dist x y :=
completion.extension₂_coe_coe uniform_continuous_dist _ _

/- Let us check that the new distance satisfies the axioms of a distance, by starting from the
properties on α and extending them to `completion α` by continuity. -/
protected lemma completion.dist_self' (x : completion α) : dist x x = 0 :=
begin
  apply induction_on x,
  { refine is_closed_eq _ continuous_const,
    exact (completion.uniform_continuous_dist'.continuous.comp
             (continuous.prod_mk continuous_id continuous_id : _) : _) },
  { assume a,
    rw [completion.dist_eq', dist_self] }
end

protected lemma completion.dist_comm' (x y : completion α) : dist x y = dist y x :=
begin
  apply induction_on₂ x y,
  { refine is_closed_eq completion.uniform_continuous_dist'.continuous _,
    exact completion.uniform_continuous_dist'.continuous.comp
      (@continuous_swap (completion α) (completion α) _ _) },
  { assume a b,
    rw [completion.dist_eq', completion.dist_eq', dist_comm] }
end

protected lemma completion.dist_triangle' (x y z : completion α) : dist x z ≤ dist x y + dist y z :=
begin
  apply induction_on₃ x y z,
  { refine is_closed_le _ (continuous.add _ _),
    { have : continuous (λp : completion α × completion α × completion α, (p.1, p.2.2)) :=
        continuous.prod_mk continuous_fst (continuous.comp continuous_snd continuous_snd),
      exact (completion.uniform_continuous_dist'.continuous.comp this : _) },
    { have : continuous (λp : completion α × completion α × completion α, (p.1, p.2.1)) :=
        continuous.prod_mk continuous_fst (continuous_fst.comp continuous_snd),
      exact (completion.uniform_continuous_dist'.continuous.comp this : _) },
    { have : continuous (λp : completion α × completion α × completion α, (p.2.1, p.2.2)) :=
        continuous.prod_mk (continuous_fst.comp continuous_snd)
                           (continuous.comp continuous_snd continuous_snd),
      exact (continuous.comp completion.uniform_continuous_dist'.continuous this : _) } },
  { assume a b c,
    rw [completion.dist_eq', completion.dist_eq', completion.dist_eq'],
    exact dist_triangle a b c }
end

/-- Elements of the uniformity (defined generally for completions) can be characterized in terms
of the distance. -/
protected lemma completion.mem_uniformity_dist' (s : set (completion α × completion α)) :
  s ∈ uniformity (completion α) ↔ (∃ε>0, ∀{a b}, dist a b < ε → (a, b) ∈ s) :=
begin
  split,
  { /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in α is an
    entourage, so it contains an ε-neighborhood of the diagonal by definition of the entourages
    in metric spaces. Then `t` contains an ε-neighborhood of the diagonal in `completion α`, as
    closed properties pass to the completion. -/
    assume hs,
    rcases mem_uniformity_is_closed hs with ⟨t, ht, ⟨tclosed, ts⟩⟩,
    have A : {x : α × α | (coe (x.1), coe (x.2)) ∈ t} ∈ uniformity α :=
      uniform_continuous_def.1 (uniform_continuous_coe α) t ht,
    rcases mem_uniformity_dist.1 A with ⟨ε, εpos, hε⟩,
    refine ⟨ε, εpos, λx y hxy, _⟩,
    have : ε ≤ dist x y ∨ (x, y) ∈ t,
    { apply induction_on₂ x y,
      { have : {x : completion α × completion α | ε ≤ dist (x.fst) (x.snd) ∨ (x.fst, x.snd) ∈ t}
               = {p : completion α × completion α | ε ≤ dist p.1 p.2} ∪ t, by ext; simp,
        rw this,
        apply is_closed_union _ tclosed,
        exact is_closed_le continuous_const completion.uniform_continuous_dist'.continuous },
      { assume x y,
        rw completion.dist_eq',
        by_cases h : ε ≤ dist x y,
        { exact or.inl h },
        { have Z := hε (not_le.1 h),
          simp only [set.mem_set_of_eq] at Z,
          exact or.inr Z }}},
    simp only [not_le.mpr hxy, false_or, not_le] at this,
    exact ts this },
  { /- Start from a set `s` containing an ε-neighborhood of the diagonal in `completion α`. To show
    that it is an entourage, we use the fact that `dist` is uniformly continuous on
    `completion α × completion α` (this is a general property of the extension of uniformly
    continuous functions). Therefore, the preimage of the ε-neighborhood of the diagonal in ℝ
    is an entourage in `completion α × completion α`. Massaging this property, it follows that
    the ε-neighborhood of the diagonal is an entourage in `completion α`, and therefore this is
    also the case of `s`. -/
    rintros ⟨ε, εpos, hε⟩,
    let r : set (ℝ × ℝ) := {p | dist p.1 p.2 < ε},
    have : r ∈ uniformity ℝ := metric.dist_mem_uniformity εpos,
    have T := uniform_continuous_def.1 (@completion.uniform_continuous_dist' α _) r this,
    simp only [uniformity_prod_eq_prod, mem_prod_iff, exists_prop,
               filter.mem_map, set.mem_set_of_eq] at T,
    rcases T with ⟨t1, ht1, t2, ht2, ht⟩,
    refine mem_sets_of_superset ht1 _,
    have A : ∀a b : completion α, (a, b) ∈ t1 → dist a b < ε,
    { assume a b hab,
      have : ((a, b), (a, a)) ∈ set.prod t1 t2 := ⟨hab, refl_mem_uniformity ht2⟩,
      have I := ht this,
      simp [completion.dist_self', real.dist_eq, completion.dist_comm'] at I,
      exact lt_of_le_of_lt (le_abs_self _) I },
    show t1 ⊆ s,
    { rintros ⟨a, b⟩ hp,
      have : dist a b < ε := A a b hp,
      exact hε this }}
end
/-- If two points are at distance 0, then they coincide. -/
protected lemma completion.eq_of_dist_eq_zero' (x y : completion α) (h : dist x y = 0) : x = y :=
begin
  /- This follows from the separation of `completion α` and from the description of
  entourages in terms of the distance. -/
  have : separated_space (completion α) := by apply_instance,
  refine separated_def.1 this x y (λs hs, _),
  rcases (completion.mem_uniformity_dist' s).1 hs with ⟨ε, εpos, hε⟩,
  rw ← h at εpos,
  exact hε εpos
end

/-- Reformulate `completion.mem_uniformity_dist` in terms that are suitable for the definition
of the metric space structure. -/
protected lemma completion.uniformity_dist''' :
  uniformity (completion α) = (⨅ε:{ε : ℝ // 0 < ε}, 𝓟 {p | dist p.1 p.2 < ε.val}) :=
begin
  ext s, rw mem_infi,
  { simp [completion.mem_uniformity_dist', set.subset_def] },
  { rintro ⟨r, hr⟩ ⟨p, hp⟩, use ⟨min r p, lt_min hr hp⟩,
    simp [lt_min_iff, (≥)] {contextual := tt} }
end

protected lemma completion.uniformity_dist'' :
  uniformity (completion α) = (⨅ ε>0, 𝓟 {p | dist p.1 p.2 < ε}) :=
by simpa [infi_subtype] using @completion.uniformity_dist''' α _

/-- Metric space structure on the completion of a pseudo_metric space. -/
instance completion.metric_space' : metric_space (completion α) :=
{ dist_self          := completion.dist_self',
  eq_of_dist_eq_zero := completion.eq_of_dist_eq_zero',
  dist_comm          := completion.dist_comm',
  dist_triangle      := completion.dist_triangle',
  to_uniform_space   := by apply_instance,
  uniformity_dist    := completion.uniformity_dist'' }

end metric

namespace uniform_space
namespace completion

@[simp] lemma norm_coe' {V} [semi_normed_group V] (v : V) :
  ∥(v : completion V)∥ = ∥v∥ :=
completion.extension_coe uniform_continuous_norm v

instance remove_me_soon (V : Type*) [semi_normed_group V] : normed_group (completion V) :=
{ dist_eq :=
  begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq (completion.uniform_continuous_extension₂ _).continuous _,
      exact continuous.comp completion.continuous_extension continuous_sub },
    { intros x y,
      rw [← completion.coe_sub, norm_coe', metric.completion.dist_eq', dist_eq_norm] }
  end,
  .. (show add_comm_group (completion V), by apply_instance),
  .. (show metric_space (completion V), by apply_instance) }

end completion
end uniform_space

end PR7066
