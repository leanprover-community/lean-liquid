import topology.sequences
import topology.algebra.normed_group
import topology.algebra.group_completion
import topology.metric_space.completion
import analysis.normed_space.normed_group_hom
import analysis.specific_limits

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

/- def j : G →+ completion G :=
⟨(coe : G → completion G), is_add_group_hom.map_zero coe, is_add_hom.map_add coe⟩

lemma j_dense : dense ((j : G →+ completion G).range : set $ completion G):=
completion.dense_range_coe

lemma completion.controlled_sum (h : completion G)
  {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ g : ℕ → G, tendsto (λ n, ∑ i in range (n+1), j (g i)) at_top (𝓝 h) ∧
               ∥j (g 0) - h∥ < b 0 ∧ ∀ n > 0, ∥g n∥ < b n :=
let ⟨g, sum_g, hg₀, H⟩ := controlled_sum_of_mem_closure_range (j_dense h) b_pos in
⟨g, sum_g, hg₀, by simpa [j] using H⟩ -/


def normed_group_hom.completion (f : normed_group_hom G H) : normed_group_hom (completion G) (completion H) :=
{ to_fun := completion.map f,
  map_add' := by { intros x y,
                   apply completion.induction_on₂ x y,
                   apply is_closed_eq,
                   exact completion.continuous_map.comp continuous_add,
                   exact (completion.continuous_map.comp  continuous_fst).add (completion.continuous_map.comp continuous_snd),
                   intros a b,
                   norm_cast,
                   simp [completion.map_coe f.uniform_continuous],
                   norm_cast },
  bound' := begin
    use ∥f∥,
    intro y,
    apply completion.induction_on y,
    exact is_closed_le (continuous_norm.comp completion.continuous_map) (continuous_const.mul continuous_norm),
    intro x,
    rw completion.map_coe f.uniform_continuous,
    simp only [f.le_op_norm x, completion.norm_coe]
  end }

def normed_group.to_compl : normed_group_hom G (completion G) :=
{ to_fun := coe,
  map_add' := by { intros x y,
                   exact is_add_hom.map_add coe x y },
  bound' := ⟨1, by simp [le_refl]⟩ }

abbreviation j := (normed_group.to_compl : normed_group_hom G $ completion G)

lemma normed_group.dense_range_to_compl : dense_range (j : G → completion G) :=
completion.dense_inducing_coe.dense

lemma normed_group_hom.ker_eq_preimage (f : normed_group_hom G H) :
  (f.ker : set G) = (f : G → H) ⁻¹' {0} :=
by { ext, erw f.mem_ker }

lemma normed_group_hom.is_closed_ker (f : normed_group_hom G H) : is_closed (f.ker : set G) :=
f.ker_eq_preimage ▸ is_closed.preimage f.continuous (t1_space.t1 0)

@[simp]
lemma normed_group_hom.completion_coe (f : normed_group_hom G H) (g : G) : f.completion g = f g:=
completion.map_coe f.uniform_continuous _

@[simp]
lemma normed_group_hom.completion_to_compl (f : normed_group_hom G H) : f.completion.comp j = j.comp f :=
begin
  ext x,
  change f.completion x = _,
  simpa
end

lemma normed_group_hom.norm_completion_le (f : normed_group_hom G H) : ∥f.completion∥ ≤ ∥f∥ :=
begin
  apply f.completion.op_norm_le_bound (norm_nonneg _),
  intro x,
  apply completion.induction_on x,
  { apply is_closed_le,
    continuity },
  { intro g,
    simp [f.le_op_norm  g] },
end

open normed_group_hom

lemma normed_group_hom.ker_le_ker_completion (f : normed_group_hom G H) :
  (j.comp $ incl f.ker).range ≤ f.completion.ker  :=
begin
  intros a h,
  replace h : ∃ y : f.ker, j (y : G) = a, by simpa using h,
  rcases h with ⟨⟨g, g_in : g ∈ f.ker⟩, rfl⟩,
  rw f.mem_ker at g_in,
  change f.completion (g : completion G) = 0,
  simp [normed_group_hom.mem_ker, f.completion_coe g, g_in, completion.coe_zero],
end

variables {K : Type*} [normed_group K]

lemma normed_group_hom.comp_range (f : normed_group_hom G H) (g : normed_group_hom H K) :
(g.comp f).range = add_subgroup.map g.to_add_monoid_hom f.range :=
begin
  erw add_monoid_hom.map_range,
  refl,
end

@[to_additive]
lemma subgroup.mem_map_of_mem {G H : Type*} [group G] [group H] {G' : subgroup G} (f : G →* H) {x : G} (hx : x ∈ G') :
  f x ∈ subgroup.map f G' :=
subgroup.mem_map.mpr ⟨x, hx, rfl⟩

lemma normed_group_hom.mem_comp_range (f : normed_group_hom G H) (g : normed_group_hom H K) (x : G) :
  g (f x) ∈ (g.comp f).range :=
begin
  rw normed_group_hom.comp_range,
  exact add_subgroup.mem_map_of_mem g.to_add_monoid_hom (mem_range_self x),
end

@[simp]
lemma normed_group.mem_range_incl (G' : add_subgroup G) (x : G) : x ∈ (incl G').range ↔ x ∈ G' :=
begin
  rw normed_group_hom.mem_range,
  split,
  { rintros ⟨y, rfl⟩,
    exact y.property },
  { intro x_in,
    exact ⟨⟨x, x_in⟩, rfl⟩ },
end

lemma normed_group.mem_closure_iff {s : set G} {x : G} : x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, ∥x - y∥ < ε :=
by simp [metric.mem_closure_iff, dist_eq_norm]

@[simp]
lemma normed_group_hom.ker_zero : (0 : normed_group_hom G H).ker = ⊤ :=
by { ext, simp [normed_group_hom.mem_ker] }

@[simp]
lemma normed_group_hom.zero_completion : (0 : normed_group_hom G H).completion = 0 :=
begin
  ext,
  apply completion.induction_on x,
  { apply is_closed_eq,
    continuity },
  { simp [normed_group_hom.mem_ker, completion.coe_zero] }
end

@[simp]
lemma normed_group_hom.range_comp_incl_top {f : normed_group_hom G H} :
(f.comp (incl (⊤ : add_subgroup G))).range = f.range :=
begin
  ext x,
  simp only [normed_group_hom.mem_range, incl_apply, normed_group_hom.comp_apply],
  split,
  { rintros ⟨⟨y, h⟩, rfl⟩,
    exact ⟨y, rfl⟩ },
  { rintros ⟨y, rfl⟩,
    exact ⟨⟨y, trivial⟩, rfl⟩ },
end

lemma normed_group_hom.ker_completion {f : normed_group_hom G H} {C : ℝ}
  (h : ∀ h ∈ f.range, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥) :
  (f.completion.ker : set $ completion G) = closure (j.comp $ incl f.ker).range :=
begin
  by_cases Hf : ∀ x, f x = 0, -- This is a bit silly, we simply avoid assuming C ≥ 0
    { have : f = 0,
      { ext, apply Hf },
      subst this,
      rw normed_group_hom.ker_zero,
      have : closure ((j : normed_group_hom G _).range : set $ completion G) = univ,
      { rw ← normed_group.dense_range_to_compl.closure_range,
        refl },
      simp [this], },
  have hC : 0 ≤ C,
  { push_neg at Hf,
    cases Hf with x hx,
    rcases h (f x) (mem_range_self x) with ⟨y, hy, hy'⟩,
    rw ← hy at hy' hx,
    exact nonneg_of_mul_nonneg_right ((norm_nonneg y).trans hy') (norm_pos_iff.mpr hx) },
  apply le_antisymm, -- Now start the actual proof
  { intros hatg hatg_in,
    rw normed_group.mem_closure_iff,
    intros ε ε_pos,
    have hCf : 0 ≤ C*∥f∥ := mul_nonneg hC (norm_nonneg _),
    have ineq : 0 < 1 + C*∥f∥, by linarith,
    set δ := ε/(1 + C*∥f∥),
    have δ_pos : δ > 0, from div_pos ε_pos ineq,
    obtain ⟨_, ⟨g : G, rfl⟩, hg : ∥hatg - g∥ < δ⟩ :=
      normed_group.mem_closure_iff.mp (completion.dense_inducing_coe.dense hatg) δ δ_pos,
    obtain ⟨g' : G, hgg' : f g' = f g, hfg : ∥g'∥ ≤ C * ∥f g∥⟩ :=
      h (f g) (mem_range_self g),
    have mem_ker : g - g' ∈ f.ker,
      by rw [f.mem_ker, f.map_sub, sub_eq_zero.mpr hgg'.symm],
    have : ∥f g∥ ≤ ∥f∥*∥hatg - g∥,
    calc
      ∥f g∥ = ∥f.completion g∥ : by rw [f.completion_coe, completion.norm_coe]
        ... = ∥f.completion (g - hatg)∥ : by simp [f.completion.map_sub, (f.completion.mem_ker _).mp hatg_in]
        ... ≤ ∥f.completion∥ * ∥(g :completion G) - hatg∥ : f.completion.le_op_norm _
        ... = ∥f.completion∥ * ∥hatg - g∥ : by rw norm_sub_rev
        ... ≤ ∥f∥ * ∥hatg - g∥ : mul_le_mul_of_nonneg_right (norm_completion_le f) (norm_nonneg _),
    have : ∥(g' : completion G)∥ ≤ C*∥f∥*∥hatg - g∥,
    calc
    ∥(g' : completion G)∥ = ∥g'∥ : completion.norm_coe _
                      ... ≤ C * ∥f g∥ : hfg
                      ... ≤ C * ∥f∥ * ∥hatg - g∥ : by { rw mul_assoc,
                                                        exact mul_le_mul_of_nonneg_left this hC},


    refine ⟨g - g', _, _⟩,
    { norm_cast,
      rw normed_group_hom.comp_range,
      apply add_subgroup.mem_map_of_mem,
      simp [mem_ker] },
    { calc ∥hatg - (g - g')∥ = ∥hatg - g + g'∥ : by abel
      ... ≤ ∥hatg - g∥ + ∥(g' : completion G)∥ : norm_add_le _ _
      ... < δ + C*∥f∥*∥hatg - g∥ : by linarith
      ... ≤ δ + C*∥f∥*δ : add_le_add_left (mul_le_mul_of_nonneg_left hg.le hCf) δ
      ... = (1 + C*∥f∥)*δ : by ring
      ... = ε :mul_div_cancel' _ ineq.ne.symm } },
  { rw ← f.completion.is_closed_ker.closure_eq,
    exact closure_mono f.ker_le_ker_completion }
end

lemma norm_le_insert' (a b : G) : ∥a∥ ≤ ∥b∥ + ∥a - b∥ :=
begin
  rw norm_sub_rev,
  exact norm_le_insert b a
end

open finset


lemma normed_group.cauchy_seq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1)
    {u : ℕ → G} (h : ∀ n, ∥u n - u (n + 1)∥ ≤ C*r^n) : cauchy_seq u :=
begin
  apply cauchy_seq_of_le_geometric _ C hr,
  simpa [dist_eq_norm] using h
end

lemma normed_group.cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → G}
  {r : ℝ} (hr : r < 1)
  (h : ∀ n, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range n, u k) :=
begin
  apply normed_group.cauchy_seq_of_le_geometric hr,
  intro n,
  rw [show ∑ k in range n, u k - ∑ k in range (n + 1), u k = - u n,
        by { simp only [finset.sum_range_succ], abel}, norm_neg],
  apply h
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

lemma normed_group.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → G} {r : ℝ} (hr : r < 1)
  (h : ∀ n, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  by_cases hC : C = 0,
  { subst hC,
    simp at h,
    simp [h, cauchy_seq_const (0 : G)] },
  have : 0 ≤ C,
  { simpa using (norm_nonneg _).trans (h 0) },
  replace hC : 0 < C,
    from (ne.symm hC).le_iff_lt.mp this,
  have : 0 ≤ r,
  { have := (norm_nonneg _).trans (h 1),
    rw pow_one at this,
    exact (zero_le_mul_left hC).mp this },
  simp_rw finset.sum_range_succ,
  have : cauchy_seq u,
  { apply tendsto.cauchy_seq,
    apply squeeze_zero_norm h,
    rw show 0 = C*0, by simp,
    exact tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 this hr) },
  exact this.add (normed_group.cauchy_series_of_le_geometric hr h),
end

lemma youpla {G : Type*} [add_comm_monoid G] {u : ℕ → G} {N : ℕ} (hu : ∀ n ≥ N, u n = 0) {n : ℕ}
  (hn : n ≥ N) : ∑ k in range (n + 1), u k = ∑ k in range (N + 1), u k :=
begin
  obtain ⟨m, rfl : n = N + m⟩ := le_iff_exists_add.mp hn,
  clear hn,
  induction m with m hm,
  { simp },
  erw [sum_range_succ, hm],
  simp [hu]
end

lemma titi {u v : ℕ → G} {N : ℕ} (huv : ∀ n ≥ N, u n = v n) (hv : cauchy_seq (λ n, ∑ k in range (n+1), v k)) :
  cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  have : (λ n, ∑ k in range (n + 1), u k) = (λ n, ∑ k in range (n + 1), (u k - v k)) + (λ n, ∑ k in range (n + 1), v k),
  { ext n,
    simp },
  rw this, clear this,
  apply cauchy_seq.add _ hv,
  apply tendsto.cauchy_seq,
  have : ∀ n ≥ N, ∑ (k : ℕ) in range (n + 1), (u k - v k) = ∑ (k : ℕ) in range (N + 1), (u k - v k),
  { intros n hn,
    rw youpla _ hn,
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

lemma normed_group.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → G} {N : ℕ} {r : ℝ}
  (hr₀ : 0 < r) (hr₁ : r < 1)
  (h : ∀ n ≥ N, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  set v : ℕ → G := λ n, if n < N then 0 else u n,
  have hC : 0 ≤ C,
    from (zero_le_mul_right $ pow_pos hr₀ N).mp ((norm_nonneg _).trans $ h N $ le_refl N),
  have : ∀ n ≥ N, u n = v n,
  { intros n hn,
    simp [v, hn, if_neg (not_lt.mpr hn)] },
  refine titi this (normed_group.cauchy_series_of_le_geometric' hr₁ _),
  { exact C },
  intro n,
  dsimp [v],
  split_ifs with H H,
  { rw norm_zero,
    exact mul_nonneg hC (pow_nonneg hr₀.le _) },
  { push_neg at H,
    exact h _ H }
end

lemma normed_group.norm_to_compl (x : G) : ∥j x∥ = ∥x∥ :=
completion.norm_coe x

lemma normed_group.norm_incl {G' : add_subgroup G} (x : G') : ∥incl _ x∥ = ∥x∥ :=
rfl

open normed_group

lemma controlled_exactness {M M₁ M₂ : Type*} [normed_group M] [normed_group M₁] [normed_group M₂]
  {f : normed_group_hom M₁ M} {C : ℝ} (hC : 0 < C) {D : ℝ}
  {g : normed_group_hom M M₂}
  (h : ∀ m ∈ g.ker, ∃ m' : M₁, f m' = m ∧ ∥m'∥ ≤ C*∥m∥)
  (h' : ∀ x ∈ g.range, ∃ y, g y = x ∧ ∥y∥ ≤ D * ∥x∥) :
  ∀ m ∈ g.completion.ker, ∀ ε > 0, ∃ m' : completion M₁, f.completion m' = m ∧ ∥m'∥ ≤ (C + ε)*∥m∥ :=
begin
  intros hatm hatm_in ε ε_pos,
  by_cases H : hatm = 0,
  { use 0,
    simp [H] },
  set hatf := f.completion,
  set i := incl g.ker,

  have norm_j_comp_i : ∀ x, ∥j.comp i x∥ = ∥x∥,
  { intro x,
    erw [norm_to_compl, norm_incl] },
  have : hatm ∈ closure ((j.comp i).range : set $ completion M),
    by rwa ← normed_group_hom.ker_completion h',

  set b : ℕ → ℝ := λ i, (1/2)^i*(ε*∥hatm∥/2)/C,
  have b_pos : ∀ i, 0 < b i,
  { intro i,
    field_simp [b, hC],
    exact div_pos (mul_pos ε_pos (norm_pos_iff.mpr H)) (mul_pos (by norm_num : (0 : ℝ) < 2^i*2) hC) },
  obtain  ⟨m, lim_m : tendsto (λ n, ∑ k in range (n + 1), j.comp i (m k)) at_top (𝓝 hatm),
        hm₀ : ∥j.comp i (m 0) - hatm∥ < b 0, hm : ∀ n > 0, ∥(j.comp i) (m n)∥ < b n⟩ :=
    controlled_sum_of_mem_closure_range this b_pos,
  have : ∀ n, ∃ m' : M₁, f m' = m n ∧ ∥m'∥ ≤ C * ∥m n∥,
  { intros n, apply h, exact (m n).property },
  choose m' hfm' hnorm_m' using this,
  set s : ℕ → completion M₁ := λ n, ∑ k in range (n+1), j (m' k),
  have : cauchy_seq s,
  { apply normed_group.cauchy_series_of_le_geometric'' (by norm_num) one_half_lt_one,
    rintro n (hn : n ≥ 1),
    calc ∥j (m' n)∥ = ∥m' n∥ : norm_to_compl _
    ... ≤ C*∥m n∥ : hnorm_m' n
    ... = C*∥j.comp i (m n)∥ : by rw norm_j_comp_i
    ... ≤ C * b n : mul_le_mul_of_nonneg_left (hm _ $ nat.succ_le_iff.mp hn).le hC.le
    ... = (1/2)^n * (ε * ∥hatm∥/2) : by simp [b, mul_div_cancel' _ hC.ne.symm]
    ... = (ε * ∥hatm∥/2) * (1/2)^n : mul_comm _ _ },
  obtain ⟨hatm' : completion M₁, hhatm'⟩ := cauchy_seq_tendsto_of_complete this,
  refine ⟨hatm', _, _⟩,
  { apply tendsto_nhds_unique _ lim_m,
    convert (hatf.continuous.tendsto hatm').comp hhatm',
    ext n,
    dsimp [s],
    rw [hatf.map_sum],
    congr,
    ext k,
    erw [f.completion_coe, hfm'],
    refl },
  { apply le_of_tendsto' (continuous_norm.continuous_at.tendsto.comp hhatm'),
    simp only [norm_j_comp_i] at hm,
    have hnorm₀ : ∥j (m' 0)∥ ≤ C*b 0 + C*∥hatm∥,
    { have := calc
      ∥m 0∥ = ∥j.comp i (m 0)∥ : by rw norm_j_comp_i
      ... ≤ ∥hatm∥ + ∥j.comp i (m 0) - hatm∥ : norm_le_insert' _ _
      ... ≤ ∥hatm∥ + b 0 : by apply add_le_add_left hm₀.le,

      calc ∥j (m' 0)∥  = ∥m' 0∥ : norm_to_compl _
      ... ≤ C*∥m 0∥ : hnorm_m' 0
      ... ≤ C*(∥hatm∥ + b 0) : mul_le_mul_of_nonneg_left this hC.le
      ... = C * b 0 + C * ∥hatm∥ : by rw [add_comm, mul_add] },

    intros n,
    have : ∑ k in range (n + 1), C * b k ≤ ε * ∥hatm∥,
    calc ∑ k in range (n + 1), C * b k = (∑ k in range (n + 1), (1 / 2) ^ k) * (ε * ∥hatm∥ / 2) : by simp only [b, mul_div_cancel' _ hC.ne.symm, ← sum_mul]
     ... ≤  2 * (ε * ∥hatm∥ / 2) : mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by nlinarith [ε_pos, norm_nonneg hatm])
     ... = ε * ∥hatm∥ : mul_div_cancel' _ two_ne_zero,

    calc ∥s n∥ ≤ ∑ k in range (n+1), ∥j (m' k)∥ : norm_sum_le _ _
    ... = ∑ k in range n, ∥j (m' (k + 1))∥ + ∥j (m' 0)∥ : sum_range_succ' _ _
    ... = ∑ k in range n, ∥m' (k + 1)∥ + ∥j (m' 0)∥ : by simp only [norm_to_compl]
    ... ≤ ∑ k in range n, C*∥m (k + 1)∥ + ∥j (m' 0)∥ : add_le_add_right (sum_le_sum (λ _ _, hnorm_m' _)) _
    ... ≤ ∑ k in range n, C*b (k+1) + (C*b 0 + C*∥hatm∥) :  add_le_add (sum_le_sum (λ k _, _)) hnorm₀
    ... = ∑ k in range (n+1), C*b k + C*∥hatm∥ :  _
    ... ≤ (C+ε)*∥hatm∥ : _,

    { exact mul_le_mul_of_nonneg_left (hm _ k.succ_pos).le hC.le },
    { rw [← add_assoc, sum_range_succ'] },
    { rw [add_comm, add_mul],
      apply add_le_add_left this } }
end

#lint
