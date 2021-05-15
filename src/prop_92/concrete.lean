import pseudo_normed_group.profinitely_filtered
import prop_92.extension_profinite
import normed_group.normed_with_aut
import for_mathlib.normed_group_hom_completion

import locally_constant.analysis

/-!
This file builds a concrete version of Proposition 9.2, with almost no category.
The exception is that `NormedGroup` is used because this is expected in
`normed_with_aut` (we could easily get rid of this but this is very mild category theory hell).
There are two independent parts. The first one is all about locally constant maps from
compact spaces to semi-normed groups. The next one forget about locally constant functions
and does abstract normed space stuff.
-/

noncomputable theory

@[simp]
lemma real.supr_zero (ι : Type*) : (⨆ i : ι, (0 : ℝ)) = 0 :=
sorry

lemma real.supr_range {α β : Type*} (f : β → α) (g : α → ℝ) :
  (⨆ a ∈ set.range f, g a) = ⨆ b, g (f b) :=
begin
  sorry
end

lemma nnreal.eq_zero_or_pos (r : nnreal) : r = 0 ∨ 0 < r :=
by admit -- can also use lt_or_eq_of_le (zero_le r)

instance semi_normed_group.inhabited (G : Type*) [semi_normed_group G] : inhabited G := ⟨0⟩

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
begin
  rw [locally_constant.norm_def, supr],

  sorry
end

@[simp]
lemma embedding.locally_constant_extend_of_empty (hX : ¬ nonempty X) (f : locally_constant X G) :
 he.locally_constant_extend f = 0 :=
begin

  sorry
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

lemma locally_constant.exists_norm_eq [nonempty X] (f : locally_constant X G) : ∃ x, ∥f∥ = ∥f x∥ :=
begin
  simp only [locally_constant.norm_def, supr],
  sorry
end

lemma locally_constant.norm_eq_iff (f : locally_constant X G) {x : X} :
  ∥f∥ = ∥f x∥ ↔ ∀ x', ∥f x'∥ ≤ ∥f x∥ :=
begin
  rw [locally_constant.norm_def],
  sorry
end

lemma locally_constant.norm_eq_iff' (f : locally_constant X G) {x : X} :
  ∥f∥ = ∥f x∥ ↔ ∀ g ∈ range f, ∥g∥ ≤ ∥f x∥ :=
by simpa only [mem_range, forall_apply_eq_imp_iff', exists_imp_distrib] using f.norm_eq_iff

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
    rw  [← real.supr_range, ← real.supr_range, he.range_locally_constant_extend f] },
  { rw [f.norm_of_empty hX],
    dsimp [embedding.locally_constant_extend, embedding.extend],
    suffices : (⨆ (y : Y), ∥(0 : G)∥) = 0,
    by simpa only [hX, dif_neg, not_false_iff, and_false],
    simp }
end

/- lemma embedding.norm_extend_eq [nonempty X] (f : locally_constant X G) :
  ∃ x, ∥f∥ = ∥f x∥ ∧ ∥he.locally_constant_extend f∥ = ∥he.locally_constant_extend f (e x)∥ :=
begin
  cases f.exists_norm_eq with x hx,
  use [x, hx],
  rwa [(he.locally_constant_extend f).norm_eq_iff', he.range_locally_constant_extend,
       he.locally_constant_extend_extends, ← f.norm_eq_iff']
end
 -/

variables
  (φ : X → Y) -- this will be φ is T⁻¹ : M_{≤ r'c}^a → M_{≤ c}^a
  {r : ℝ≥0} {V : NormedGroup} [normed_with_aut r V] -- this is indeed V!

include r

lemma locally_constant.norm_map_aut (g : locally_constant Y V) : ∥g.map T.hom∥ = r*∥g∥ :=
begin
  by_cases hY : nonempty Y,
  { resetI,
    cases g.exists_norm_eq with y hy,
    erw [hy, ← norm_T, locally_constant.norm_eq_iff],
    intro y',
    erw [norm_T, norm_T],
    cases lt_or_eq_of_le (zero_le r) with hr hr,
    { simp [hr, ← hy, g.norm_apply_le] },
    { simp [hr.symm] } },
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

lemma limit : tendsto (λ N, ((he.g hφ f N).comap e).map T.inv - ((he.g hφ f N).comap φ)) at_top (𝓝 f) :=
begin
  -- follows easily from one and norm_h
  sorry
end

lemma cauchy_seq_g : cauchy_seq (he.g hφ f) :=
sorry -- follows easily from norm_h and geometry series

lemma norm_g_le (N : ℕ) : ∥he.g hφ f N∥ ≤ r/(1 - r) * ∥f∥ :=
sorry -- follows easily from norm_h and geometric series

end locally_constant_stuff

section general_completion_stuff
open filter
open_locale topological_space

-- Now we want an abstract machine where we can plug the sequence g from the previous section.

variables {M₁ : Type*} [semi_normed_group M₁] {M₂ : Type*} [semi_normed_group M₂]
          (f : normed_group_hom M₁ M₂)

/-
The next lemma is a version of normed_group/controlled_exactness.lean but `f` is not assumed to be
surjective. We'll need to abstract part of that older proof
-/

lemma bar {C ε : ℝ} (hε : 0 < ε)
  (h : ∀ m₂ : M₂, ∃ g : ℕ → M₁, cauchy_seq g ∧ tendsto (f ∘ g) at_top (𝓝 m₂) ∧ ∀ n, ∥g n∥ ≤ C*∥f∥) :
  ∀ m₂, ∃ m₁, f.completion m₁ = m₂ ∧ ∥m₁∥ ≤ C*(1+ε)*∥m₂∥ :=
begin

  sorry
end

end general_completion_stuff
