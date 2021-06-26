import pseudo_normed_group.profinitely_filtered
import prop_92.extension_profinite
import normed_group.normed_with_aut

import for_mathlib.normed_group_hom_completion
import for_mathlib.normed_group_hom

import locally_constant.analysis

/-!
This file builds a concrete version of Proposition 9.2, with almost no category.
The exception is that `SemiNormedGroup` is used because this is expected in
`normed_with_aut` (we could easily get rid of this but this is very mild category theory hell).
There are two independent parts. The first one is all about locally constant maps from
compact spaces to seminormed groups. The next one forget about locally constant functions
and does abstract normed space stuff.
-/

noncomputable theory

section
open finset
open_locale big_operators

-- Why can't I find this in mathlib?!?
lemma partial_sum_geom {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (n : ℕ) : (∑ k in range n, r^k) = (1 - r^n)/(1 - r) :=
begin
  refine (eq_div_iff (sub_ne_zero.mpr hr'.ne')).mpr _,
  induction n with n ih,
  { simp },
  { rw [sum_range_succ, add_mul, ih],
    ring_exp }
end

-- Why can't I find this in mathlib?!?
lemma partial_sum_geom_le {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (n : ℕ) : (∑ k in range n, r^k) ≤ 1/(1 - r) :=
begin
  rw partial_sum_geom hr hr',
  exact div_le_div zero_le_one (sub_le_self _ (pow_nonneg hr n)) (sub_pos.mpr hr') rfl.le,
end

lemma norm_sum_le_of_le_geom {α : Type*} [semi_normed_group α] {r C : ℝ} (hC : 0 ≤ C)
  (hr₀ : 0 ≤ r) (hr₁ : r < 1) {f : ℕ → α} (h : ∀ n, ∥f n∥ ≤ C*r^n) {n : ℕ} :
  ∥∑ k in range n, f k∥ ≤ C/(1-r) :=
begin
calc
  ∥∑ k in range n, f k∥ ≤ ∑ k in range n, ∥f k∥ : norm_sum_le _ _
  ... ≤ ∑ k in range n, C*r^k   : sum_le_sum (λ k hk, h k)
  ... = C*(∑ k in range n, r^k) : (range n).sum_hom (has_mul.mul C)
  ... ≤ C*(1/(1-r))             : mul_le_mul_of_nonneg_left (partial_sum_geom_le hr₀ hr₁ n) hC
  ... = C/(1-r)                 : mul_one_div C (1 - r)
end

end

open set

-- the following proof is overkill but nice
lemma real.Sup_mem_of_finite {s : set ℝ} (hs : s.finite) (hs' : s.nonempty):
  Sup s ∈ s :=
is_compact.Sup_mem hs.is_compact hs'

@[simp]
lemma real.supr_zero (ι : Type*) : (⨆ i : ι, (0 : ℝ)) = 0 :=
begin
  rw supr,
  by_cases hι : nonempty ι,
  { resetI, rw [set.range_const, cSup_singleton] },
  { rw [set.range_eq_empty.mpr hι, real.Sup_empty] }
end

-- Move me
lemma real.Sup_eq {s : set ℝ} (hs : s.nonempty) (hs' : ∃ x, ∀ y ∈ s, y ≤ x) {x : ℝ} :
  Sup s = x ↔ ∀ y, x ≤ y ↔ (∀ z ∈ s, z ≤ y) :=
begin
  classical,
  rw real.Sup_def,
  rw dif_pos,
  { let x₀ := classical.some (real.exists_sup s hs hs'),
    change x₀ = x ↔ _,
    have H : ∀ y, x₀ ≤ y ↔ ∀ z ∈ s, z ≤ y := classical.some_spec (real.exists_sup s hs hs'),
    split,
    { dsimp [x₀],
      rintro rfl,
      exact H },
    { intro h,
      replace H : ∀ y, x₀ ≤ y ↔ x ≤ y,
      { intro y,
        rw [h, H] },
      apply le_antisymm,
      { exact (H _).mpr (le_refl _) },
      { exact (H _).mp (le_refl _) } } },
  { exact ⟨hs, hs'⟩ }
end

-- Move me
lemma is_lub_iff {α : Type*} [preorder α] {s : set α} {x : α} :
  is_lub s x ↔ ∀ y, x ≤ y ↔ ∀ z ∈ s, z ≤ y :=
begin
  split,
  { rintros ⟨h₁, h₂⟩ y,
    exact ⟨λ hxy z z_in, (h₁ z_in).trans hxy, λ h, h₂ h⟩ },
  { intro H,
    exact ⟨λ y y_in, (H x).mp (le_refl x) y y_in, λ z hz, by rwa H⟩ }
end

-- Move me
lemma real.Sup_eq' {s : set ℝ} (hs : s.nonempty) (hs' : ∃ x, ∀ y ∈ s, y ≤ x) {x : ℝ} :
  Sup s = x ↔ (∀ y ∈ s, y ≤ x) ∧ ∀ z, (∀ y ∈ s, y ≤ z) → x ≤ z :=
begin
  rw real.Sup_eq hs hs',
  change _ ↔ is_lub _ _,
  rw is_lub_iff
end

lemma real.supr_comp {α β : Type*} (f : β → α) (g : α → ℝ) :
  (⨆ b, g (f b)) = Sup (g '' range f) :=
begin
  change Sup _ = _,
  congr,
  ext x,
  simp,
end


lemma nnreal.eq_zero_or_pos (r : nnreal) : r = 0 ∨ 0 < r :=
(lt_or_eq_of_le $ zero_le r).elim (λ h, or.inr h) (λ h, or.inl h.symm)

instance semi_normed_group.inhabited (G : Type*) [semi_normed_group G] : inhabited G := ⟨0⟩

section general_completion_stuff
open filter uniform_space
open_locale topological_space

-- Now we want an abstract machine where we can plug the sequence g from the previous section.

variables {M₁ : Type*} [semi_normed_group M₁] {M₂ : Type*} [semi_normed_group M₂]
          (f : normed_group_hom M₁ M₂)

-- PR very close to the definition of cauchy_seq
lemma cauchy_seq.map {β : Type*} [semilattice_sup β]
  {α : Type*} [uniform_space α] {γ : Type*} [uniform_space γ]
  {u : β → α} {f : α → γ} (hu : cauchy_seq u) (hf : uniform_continuous f) :
  cauchy_seq (f ∘ u) :=
begin
  change cauchy _,
  rw ← map_map,
  exact cauchy.map hu hf
end

-- actually not used here, but should go somewhere
lemma normed_group_hom.coe_range : (f.range : set M₂) = set.range f :=
by { erw add_monoid_hom.coe_range, refl }

lemma bar {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
  (h : ∀ m₂ : M₂, ∃ g : ℕ → M₁, cauchy_seq g ∧ tendsto (f ∘ g) at_top (𝓝 m₂) ∧ ∀ n, ∥g n∥ ≤ C*∥m₂∥) :
  ∀ hatm₂ : completion M₂, ∃ m₁, f.completion m₁ = hatm₂ ∧ ∥m₁∥ ≤ (C+ε)*∥hatm₂∥ :=
begin
  intro hatm₂,
  refine controlled_closure_range_of_complete normed_group.norm_to_compl hC hε _ (normed_group.dense_range_to_compl _),
  intro m₂,
  rcases h m₂ with ⟨g, cauchy_g, lim_g, bound_g⟩,
  have : cauchy_seq (j ∘ g),
    from cauchy_g.map j.uniform_continuous,
  rcases cauchy_seq_tendsto_of_complete this with ⟨y, hy⟩,
  refine ⟨y, _, _⟩,
  { have lim : tendsto ((f.completion.comp j) ∘ g) at_top (𝓝 (f.completion y)),
      from (f.completion.continuous.tendsto _).comp hy,
    rw f.completion_to_compl at lim,
    have : tendsto ((j ∘ f) ∘ g) at_top (𝓝 (j m₂)) := (j.continuous.tendsto _).comp lim_g,
    exact tendsto_nhds_unique lim this },
  { refine le_of_tendsto' (tendsto_norm.comp hy) (_ : ∀ n, ∥j (g n)∥ ≤ C * ∥m₂∥),
    intro n,
    rw normed_group.norm_to_compl,
    apply bound_g }
end

end general_completion_stuff

section locally_constant_stuff
open topological_space normed_with_aut set
open_locale nnreal big_operators

local attribute [instance] locally_constant.semi_normed_group

/- Comment below indicate how this will be applied to Prop 9.2 -/
variables
  /- this will be M_{≤ r'c}^a -/
  {X : Type*} [topological_space X] [compact_space X]
  /- this will be M_{≤ c}^a -/
  {Y : Type*} [topological_space Y] [compact_space Y] [t2_space Y] [totally_disconnected_space Y]
  /- This will be inclusion -/
  {e : X → Y} (he : embedding e)
  /- This is used only for premilinary lemma not need the T action on V -/
  {G : Type*} [semi_normed_group G]


@[simp]
lemma locally_constant.norm_of_empty (hX : ¬ nonempty X) (f : locally_constant X G) : ∥f∥ = 0 :=
by rw [locally_constant.norm_def, supr, range_eq_empty.mpr hX, real.Sup_empty]

@[simp]
lemma embedding.locally_constant_extend_of_empty (hX : ¬ nonempty X) (f : locally_constant X G) :
 he.locally_constant_extend f = 0 :=
begin
  ext y, dsimp [embedding.locally_constant_extend, embedding.extend],
  rw dif_neg,
  { refl },
  { intro h, exact hX h.2 }
end

@[simp]
lemma locally_constant.map_zero {Z : Type*} (g : G → Z) :
  (0 : locally_constant X G).map g = locally_constant.const X (g 0) :=
begin
  ext x,
  simp only [function.comp_app, locally_constant.map_apply, locally_constant.zero_apply],
  refl,
end

@[simp]
lemma locally_constant.norm_const [h : nonempty X] (g : G) : ∥locally_constant.const X g∥ = ∥g∥ :=
by simp only [locally_constant.norm_def, locally_constant.const, csupr_const,
    function.const_apply, locally_constant.coe_mk]

@[simp]
lemma locally_constant.norm_zero : ∥(0 : locally_constant X G)∥ = 0 :=
by simp only [locally_constant.norm_def, norm_zero, real.supr_zero, locally_constant.zero_apply]

@[simp]
lemma locally_constant.norm_const_zero : ∥locally_constant.const X (0 : G)∥ = 0 :=
locally_constant.norm_zero

-- Should go in mathlib topology/algebra/ordered, next to is_compast.exists_Sup_image_eq
lemma continuous.exists_forall_le_of_compact {X : Type*} [topological_space X] [compact_space X] [nonempty X]
{β : Type*} [conditionally_complete_linear_order β] [topological_space β] [order_topology β] {f : X → β}
(hf : continuous f) : ∃ x, Sup (range f) = f x :=
by simpa using compact_univ.exists_Sup_image_eq univ_nonempty hf.continuous_on

lemma locally_constant.exists_norm_eq [nonempty X] (f : locally_constant X G) : ∃ x, ∥f∥ = ∥f x∥ :=
(continuous_norm.comp f.continuous).exists_forall_le_of_compact

lemma locally_constant.norm_eq_iff (f : locally_constant X G) {x : X} :
  ∥f∥ = ∥f x∥ ↔ ∀ x', ∥f x'∥ ≤ ∥f x∥ :=
begin
  have fin_range : (range (λ (x : X), ∥f x∥)).finite,
  { rw range_comp,
    apply finite.image,
    exact f.range_finite },
  have bound : ∃ b, ∀ y ∈ range (λ (x : X), ∥f x∥), y ≤ b,
    from exists_upper_bound_image _ _ fin_range,
  rw [locally_constant.norm_def],
  split,
  { intros h x',
    rw ← h,
    exact real.le_Sup _ bound (mem_range_self _) } ,
  { intro h,
    erw real.Sup_eq _ bound,
    { intro y,
      rw forall_range_iff,
      split,
      { intros h' x',
        exact (h x').trans h' },
      { exact λ i, i x } },
    { exact ⟨∥f x∥, mem_range_self _⟩ } }
end

lemma locally_constant.norm_eq_iff' (f : locally_constant X G) {x : X} :
  ∥f∥ = ∥f x∥ ↔ ∀ g ∈ range f, ∥g∥ ≤ ∥f x∥ :=
by rw [forall_range_iff, locally_constant.norm_eq_iff]

lemma locally_constant.norm_comap_le {α : Type*} [topological_space α] [compact_space α]
  (f : locally_constant X G) {g : α → X} (h : continuous g) : ∥f.comap g∥ ≤ ∥f∥ :=
locally_constant.comap_hom_norm_noninc g h f

lemma locally_constant.comap_map {W X Y Z : Type*} [topological_space W] [topological_space X] [topological_space Y]
  (f : locally_constant X Y) (g : W → X) (h : Y → Z) (hg : continuous g) : (f.comap g).map h = (f.map h).comap g :=
by { ext, simp [hg] }

lemma locally_constant.map_comp' {W X Y Z : Type*} [topological_space W]
  (f : locally_constant W X) (g : X → Y) (h : Y → Z) : (f.map g).map h = f.map (h ∘ g) :=
rfl

lemma embedding.norm_extend (f : locally_constant X G) : ∥he.locally_constant_extend f∥ = ∥f∥ :=
begin
  by_cases hX : nonempty X,
  { resetI,
    change (⨆ y : Y, _) = (⨆ x : X, _),
    rw [real.supr_comp, real.supr_comp, he.range_locally_constant_extend f] },
  { rw [f.norm_of_empty hX],
    dsimp [embedding.locally_constant_extend, embedding.extend],
    suffices : (⨆ (y : Y), ∥(0 : G)∥) = 0,
    by simpa only [hX, dif_neg, not_false_iff, and_false],
    simp }
end

variables
  (φ : X → Y) -- this will be φ is T⁻¹ : M_{≤ r'c}^a → M_{≤ c}^a
  {r : ℝ≥0} {V : SemiNormedGroup} [normed_with_aut r V] -- this is indeed V!

include r

lemma locally_constant.norm_map_aut (g : locally_constant Y V) : ∥g.map T.hom∥ = r*∥g∥ :=
begin
  by_cases hY : nonempty Y,
  { resetI,
    cases g.exists_norm_eq with y hy,
    erw [hy, ← norm_T, locally_constant.norm_eq_iff],
    intro y',
    erw [norm_T, norm_T],
    cases r.eq_zero_or_pos with hr hr,
    { simp [hr] },
    { simp [hr, ← hy, g.norm_apply_le] } },
  { simp [hY] },
end

@[simp]
lemma normed_with_aut.T_inv_T_hom : (T.inv : V → V) ∘ T.hom = id :=
begin
  ext,
  simp,
end

open locally_constant
variables {φ} (hφ : continuous φ)

include hφ

noncomputable
def embedding.h (f : locally_constant X V) : ℕ → locally_constant Y V
| 0     := map_hom T.hom (he.locally_constant_extend f)
| (i+1) := map_hom T.hom (he.locally_constant_extend $ (comap_hom φ hφ $ embedding.h i))

variables (f : locally_constant X V)

lemma norm_h (i : ℕ) : ∥he.h hφ f i∥ ≤ r^(i+1)*∥f∥ :=
begin
  induction i with i ih ; dsimp [embedding.h],
  { rw [locally_constant.norm_map_aut, he.norm_extend, zero_add, pow_one] },
  { rw [locally_constant.norm_map_aut, he.norm_extend, pow_succ, mul_assoc],
    exact mul_le_mul_of_nonneg_left (((he.h hφ f i).norm_comap_le hφ).trans ih) r.coe_nonneg },
end

open finset

def embedding.g (f : locally_constant X V) (N : ℕ) : locally_constant Y V :=
∑ i in range (N + 1), he.h hφ f i


/-- T⁻¹ g_N e - g_N φ = f - h_N φ-/
lemma one (hφ : continuous φ) (N : ℕ) :
  map_hom T.inv (comap_hom e he.continuous (he.g hφ f N)) - (comap_hom φ hφ (he.g hφ f N)) =
  f - comap_hom φ hφ (he.h hφ f N) :=
begin
  induction N with N ih,
  { dsimp [embedding.g],
    simp only [embedding.h, finset.sum_singleton, sub_left_inj],
    ext x,
    simp [he.continuous, he.locally_constant_extend_extends] },
  { set c_φ : normed_group_hom (locally_constant Y V) (locally_constant X V) := comap_hom φ hφ,
    set c_e : normed_group_hom (locally_constant Y V) (locally_constant X V) := comap_hom e he.continuous,
    set m_T : normed_group_hom (locally_constant X V) (locally_constant X V) := map_hom T.inv,
    set G := he.g hφ f,
    set H := he.h hφ f,
    change m_T _ - _ = _,
    rw sub_eq_iff_eq_add at ih,
    dsimp [embedding.g, embedding.h],
    change m_T (c_e ∑ i in range (N.succ + 1), H i) -
      c_φ ∑ i in range (N.succ + 1), H i = _,
    erw [finset.sum_range_succ, normed_group_hom.map_add, normed_group_hom.map_add, normed_group_hom.map_add, ih],
    change f - c_φ (H N) + c_φ (G N) + m_T (c_e (H N.succ)) - (c_φ (G N) + c_φ (H N.succ)) =  f - comap φ (H N.succ),
    dsimp [H, embedding.h],
    rw [← (he.locally_constant_extend $ comap φ $ H N).comap_map  e T.hom he.continuous,
        he.comap_locally_constant_extend, locally_constant.map_comp', normed_with_aut.T_inv_T_hom],
    simp [H],
    abel },
end

open filter
open_locale topological_space

variables [fact ((r : ℝ) < 1)]

lemma limit : tendsto (λ N, map_hom T.inv (comap_hom e he.continuous (he.g hφ f N)) - (comap_hom φ hφ (he.g hφ f N))) at_top (𝓝 f) :=
begin
  simp_rw one,
  rw show 𝓝 f = 𝓝 (f - 0), by simp,
  refine tendsto_const_nhds.sub _,
  apply squeeze_zero_norm,
  intro n,
  apply ((he.h hφ f n).norm_comap_le hφ).trans (norm_h he hφ _ _),
  rw ← zero_mul (∥f∥),
  apply tendsto.mul_const,
  rw tendsto_add_at_top_iff_nat,
  exact tendsto_pow_at_top_nhds_0_of_lt_1 r.coe_nonneg (fact.out _)
end

lemma cauchy_seq_g : cauchy_seq (he.g hφ f) :=
begin
  apply cauchy_seq_of_le_geometric r (r^2*∥f∥) (fact.out _),
  intro n,
  dsimp [embedding.g],
  rw [dist_eq_norm, sum_range_succ _ (n+1), sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg],
  convert norm_h he hφ f (n+1) using 1,
  ring_exp
end


lemma norm_g_le (N : ℕ) : ∥he.g hφ f N∥ ≤ r/(1 - r) * ∥f∥ :=
begin
  have : ∀ (n : ℕ), ∥he.h hφ f n∥ ≤ r * ∥f∥ * r ^ n,
  { intro n,
    convert norm_h he hφ f n using 1,
    ring_exp },
  convert norm_sum_le_of_le_geom (mul_nonneg r.coe_nonneg $ norm_nonneg f) r.coe_nonneg (fact.out _) this using 1,
  exact div_mul_eq_mul_div _ _ _,
end

open uniform_space

lemma concrete_92 [fact (0 < r)] (f : completion (locally_constant X V)) {ε : ℝ} (hε : 0 < ε) :
  ∃ g : completion (locally_constant Y V),
    ((map_hom T.inv).comp (comap_hom e he.continuous) - comap_hom φ hφ).completion g = f ∧
    ∥g∥ ≤ (r/(1-r) + ε)*∥f∥ :=
begin
  have : (0 : ℝ) < r / (1 - r),
  { have : 0 < r := fact.out _,
    apply div_pos,
    { exact_mod_cast this },
    { exact sub_pos.mpr (fact.out _) } },
  apply bar _ this hε,
  intro m₂,
  exact ⟨he.g hφ m₂, cauchy_seq_g he hφ m₂, limit he hφ m₂, norm_g_le he hφ m₂⟩
end

end locally_constant_stuff
