import algebra.punit_instances
import topology.algebra.group

import pseudo_normed_group.basic

import hacks_and_tricks.type_pow
import facts

open pseudo_normed_group
open_locale nnreal big_operators

local attribute [instance] type_pow

/-- A *profinitely filtered pseudo normed topological group* is
* an abelian group `M` with an increasing filtration `filtration M c, c : ℝ≥0` such that
* `filtration M c` is a profinite set
* `M` is pseudo normed, so `0 ∈ filtration M c`, `-(filtration M c = filtration M c`,
  and `x₁ ∈ filtration M c₁, x₂ ∈ filtration M c₂ → (x₁ + x₂) ∈ filtration M (c₁ + c₂)`
* (bounded) addition and negation are continuous.

Morphisms are continuous and bounded homomorphisms. -/
class profinitely_filtered_pseudo_normed_group (M : Type*)
  extends pseudo_normed_group M :=
[topology : ∀ c, topological_space (filtration c)]
[t2 : ∀ c, t2_space (filtration c)]
[td : ∀ c, totally_disconnected_space (filtration c)]
[compact : ∀ c, compact_space (filtration c)]
(continuous_add' : ∀ (c₁ c₂),
  continuous (add' : filtration c₁ × filtration c₂ → filtration (c₁ + c₂)))
(continuous_neg' : ∀ c, continuous (neg' : filtration c → filtration c))
(continuous_cast_le : ∀ (c₁ c₂) [h : fact (c₁ ≤ c₂)],
  continuous (cast_le : filtration c₁ → filtration c₂))

namespace profinitely_filtered_pseudo_normed_group

variables {M M₁ M₂ M₃ : Type*}
variables [profinitely_filtered_pseudo_normed_group M]
variables [profinitely_filtered_pseudo_normed_group M₁]
variables [profinitely_filtered_pseudo_normed_group M₂]
variables [profinitely_filtered_pseudo_normed_group M₃]

instance (c : ℝ≥0) : topological_space (filtration M c) := topology c
instance (c : ℝ≥0) : t2_space (filtration M c) := t2 c
instance (c : ℝ≥0) : totally_disconnected_space (filtration M c) := td c
instance (c : ℝ≥0) : compact_space (filtration M c) := compact c

lemma is_closed_map_cast_le (c₁ c₂) [h : fact (c₁ ≤ c₂)] :
  is_closed_map (@pseudo_normed_group.cast_le M _ _ _ h) :=
(continuous_cast_le c₁ c₂).is_closed_map

lemma closed_embedding_cast_le (c₁ c₂) [h : fact (c₁ ≤ c₂)] :
  closed_embedding (@pseudo_normed_group.cast_le M _ _ _ h) :=
closed_embedding_of_continuous_injective_closed
  (continuous_cast_le c₁ c₂) (injective_cast_le c₁ c₂) (is_closed_map_cast_le c₁ c₂)

lemma embedding_cast_le (c₁ c₂) [h : fact (c₁ ≤ c₂)] :
  embedding (@pseudo_normed_group.cast_le M _ _ _ h) :=
(closed_embedding_cast_le c₁ c₂).to_embedding

end profinitely_filtered_pseudo_normed_group

section
set_option old_structure_cmd true

structure profinitely_filtered_pseudo_normed_group_hom (M₁ M₂ : Type*)
  [profinitely_filtered_pseudo_normed_group M₁]
  [profinitely_filtered_pseudo_normed_group M₂]
  extends M₁ →+ M₂ :=
(bound' : ∃ C, ∀ c x, x ∈ filtration M₁ c → to_fun x ∈ filtration M₂ (C * c))
(continuous' : ∀ ⦃c₁ c₂⦄ (f₀ : filtration M₁ c₁ → filtration M₂ c₂)
  (h : ∀ x, to_fun ↑x = f₀ x), continuous f₀)

end

attribute [nolint doc_blame] profinitely_filtered_pseudo_normed_group_hom.mk
  profinitely_filtered_pseudo_normed_group_hom.to_add_monoid_hom

namespace profinitely_filtered_pseudo_normed_group_hom

open profinitely_filtered_pseudo_normed_group

variables {M M₁ M₂ M₃ : Type*}
variables [profinitely_filtered_pseudo_normed_group M]
variables [profinitely_filtered_pseudo_normed_group M₁]
variables [profinitely_filtered_pseudo_normed_group M₂]
variables [profinitely_filtered_pseudo_normed_group M₃]
variables (f g : profinitely_filtered_pseudo_normed_group_hom M₁ M₂)

instance : has_coe_to_fun (profinitely_filtered_pseudo_normed_group_hom M₁ M₂) :=
⟨_, profinitely_filtered_pseudo_normed_group_hom.to_fun⟩

@[simp] lemma coe_mk (f) (h₁) (h₂) (h₃) (h₄) :
  ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : profinitely_filtered_pseudo_normed_group_hom M₁ M₂) = f :=
rfl

@[simp] lemma mk_to_monoid_hom (f) (h₁) (h₂) (h₃) (h₄) :
  (⟨f, h₁, h₂, h₃, h₄⟩ :
    profinitely_filtered_pseudo_normed_group_hom M₁ M₂).to_add_monoid_hom =
    ⟨f, h₁, h₂⟩ := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sum {ι : Type*} (x : ι → M₁) (s : finset ι) :
  f (∑ i in s, x i) = ∑ i in s, f (x i) :=
f.to_add_monoid_hom.map_sum _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

/-- Make a profinitely filtered pseudo normed group hom
from a group hom and a proof that it is bounded and continuous. -/
def mk' (f : M₁ →+ M₂) (h : ∃ C, ∀ c, ∃ (H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c)),
    @continuous (filtration M₁ c) (filtration M₂ (C * c)) _ _ (λ x, ⟨f x, H x x.2⟩)) :
  profinitely_filtered_pseudo_normed_group_hom M₁ M₂ :=
{ bound' := by { obtain ⟨C, hC⟩ := h, refine ⟨C, λ c, (hC c).some⟩ },
  continuous' := λ c₁ c₂ f₀ hf₀,
  begin
    obtain ⟨C, hC⟩ := h,
    obtain ⟨_, H⟩ := hC c₁,
    haveI : fact ((C * c₁) ≤ max (C * c₁) c₂) := le_max_left _ _,
    haveI : fact (c₂ ≤ max (C * c₁) c₂) := le_max_right _ _,
    rw (embedding_cast_le c₂ (max (C * c₁) c₂)).continuous_iff,
    rw (embedding_cast_le (C * c₁) (max (C * c₁) c₂)).continuous_iff at H,
    convert H using 1,
    ext, dsimp, rw ← hf₀, refl
  end,
  .. f }

@[simp] lemma coe_mk' (f : M₁ →+ M₂) (h) : ⇑(mk' f h) = f := rfl

lemma bound : ∃ C, ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c) := f.bound'

protected lemma continuous ⦃c₁ c₂⦄ (f₀ : filtration M₁ c₁ → filtration M₂ c₂) (h : ∀ x, f ↑x = f₀ x) :
  continuous f₀ := f.continuous' f₀ h

-- /-- `f.level c` is the function `filtration M₁ c → filtration M₂ c`
-- induced by a `profinitely_filtered_pseudo_normed_group_hom M₁ M₂`. -/
-- @[simps] def level (c : ℝ≥0) (x : filtration M₁ c) : filtration M₂ c := ⟨f x, f.strict x.2⟩

-- lemma level_continuous (c : ℝ≥0) : continuous (f.level c) := f.continuous' c

variables {f g}

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance : has_zero (profinitely_filtered_pseudo_normed_group_hom M₁ M₂) :=
⟨mk' (0 : M₁ →+ M₂) ⟨0, λ c, ⟨λ _ _, zero_mem_filtration _, @continuous_const _ _ _ _ 0⟩⟩⟩

instance : inhabited (profinitely_filtered_pseudo_normed_group_hom M₁ M₂) := ⟨0⟩

lemma coe_inj ⦃f g : profinitely_filtered_pseudo_normed_group_hom M₁ M₂⦄ (h : (f : M₁ → M₂) = g) :
  f = g :=
by cases f; cases g; cases h; refl

/-- The identity function as `profinitely_filtered_pseudo_normed_group_hom`. -/
@[simps] def id : profinitely_filtered_pseudo_normed_group_hom M M :=
mk' (add_monoid_hom.id _) $
begin
  refine ⟨1, λ c, ⟨_, _⟩⟩,
  { intros, rwa one_mul },
  haveI : fact (1 * c ≤ c) := by { apply le_of_eq, rw one_mul },
  rw (embedding_cast_le (1 * c) c).continuous_iff,
  convert continuous_id, ext, refl
end

/-- The composition of `profinitely_filtered_pseudo_normed_group_hom`s. -/
@[simps] def comp
  (g : profinitely_filtered_pseudo_normed_group_hom M₂ M₃)
  (f : profinitely_filtered_pseudo_normed_group_hom M₁ M₂) :
  profinitely_filtered_pseudo_normed_group_hom M₁ M₃ :=
mk' (g.to_add_monoid_hom.comp f.to_add_monoid_hom) $
begin
  obtain ⟨Cf, hCf⟩ := f.bound,
  obtain ⟨Cg, hCg⟩ := g.bound,
  refine ⟨Cg * Cf, λ c, ⟨_, _⟩⟩,
  { intros x hx, rw mul_assoc, exact hCg (hCf hx) },
  let f₀ : filtration M₁ c → filtration M₂ (Cf * c) := λ x, ⟨f x, hCf x.2⟩,
  have hf₀ : continuous f₀ := f.continuous _ (λ x, rfl),
  let g₀ : filtration M₂ (Cf * c) → filtration M₃ (Cg * (Cf * c)) := λ x, ⟨g x, hCg x.2⟩,
  have hg₀ : continuous g₀ := g.continuous _ (λ x, rfl),
  haveI : fact (Cg * Cf * c ≤ Cg * (Cf * c)) := by { apply le_of_eq, rw mul_assoc },
  rw (embedding_cast_le (Cg * Cf * c) (Cg * (Cf * c))).continuous_iff,
  exact hg₀.comp hf₀
end

end profinitely_filtered_pseudo_normed_group_hom

namespace punit

-- move this
instance (X : Type*) [subsingleton X] (p : X → Prop) :
  subsingleton (subtype p) :=
⟨λ x y, subtype.ext $ subsingleton.elim _ _⟩

instance : profinitely_filtered_pseudo_normed_group punit :=
{ filtration := λ _, set.univ,
  filtration_mono := λ _ _ _, set.subset_univ _,
  zero_mem_filtration := λ _, set.mem_univ _,
  neg_mem_filtration := λ _ _ _, set.mem_univ _,
  add_mem_filtration := λ _ _ _ _ _ _, set.mem_univ _,
  continuous_add' := λ _ _,  continuous_of_discrete_topology,
  continuous_neg' := λ _, continuous_of_discrete_topology,
  continuous_cast_le := λ _ _ _, continuous_of_discrete_topology }

end punit

section continuity

variables {M M₁ M₂ M₃ : Type*}

namespace pseudo_normed_group

/-- Helper function for pseudo normed groups.
`pow_incl` is the natural inclusion function `(filtration M c)^n → M^n`.
Note that `(filtration M c)^n` is not the same type as `filtration (M^n) c`,
although they are naturally equivalent. -/
def pow_incl {n : ℕ} {c : ℝ≥0} [pseudo_normed_group M] :
  (filtration M c : Type*)^n → M^n :=
λ x j, x j

lemma pow_incl_injective {n : ℕ} {c : ℝ≥0} [pseudo_normed_group M] :
  function.injective (@pow_incl M n c _) :=
λ x y h, funext $ λ j, subtype.coe_injective $ congr_fun h j

@[simp] lemma pow_incl_apply {n : ℕ} {c : ℝ≥0} [pseudo_normed_group M]
  (x : (filtration M c : Type*)^n) (j : fin n) :
  pow_incl x j = x j := rfl

end pseudo_normed_group

open pseudo_normed_group profinitely_filtered_pseudo_normed_group

variables [profinitely_filtered_pseudo_normed_group M]
variables [profinitely_filtered_pseudo_normed_group M₁]
variables [profinitely_filtered_pseudo_normed_group M₂]
variables [profinitely_filtered_pseudo_normed_group M₃]

/-- A function `f : M₁ → M₂` between profinitely filtered pseudo normed groups
is continuous if it is continuous when restricted to the filtration sets.

Implementation detail: to avoid diamonds of topologies on `filtration M c`
we avoid `topological_space M`.
We therefore give a hands on definition of continuity. -/
def pfpng_ctu (f : M₁ → M₂) : Prop :=
∀ ⦃c₁ c₂⦄ (f₀ : filtration M₁ c₁ → filtration M₂ c₂)
  (h : ∀ x, f ↑x = f₀ x), continuous f₀

section pfpng_ctu

lemma pfpng_ctu_const (y : M₂) : pfpng_ctu (λ x : M₁, y) :=
begin
  intros c₁ c₂ f₀ h,
  suffices : f₀ = λ x, f₀ ⟨0, zero_mem_filtration _⟩,
  { rw this, exact continuous_const },
  ext1 x,
  apply subtype.coe_injective,
  rw [← h, ← h]
end

lemma pfpng_ctu.neg {f : M₁ → M₂} (hf : pfpng_ctu f) :
  pfpng_ctu (-f) :=
begin
  intros c₁ c₂ f₀ h,
  let g := neg' ∘ f₀,
  have hg : f₀ = neg' ∘ g, { ext, simp [neg_neg] },
  rw hg,
  refine (continuous_neg' c₂).comp (hf g _),
  intro x,
  specialize h x,
  simp only [g, ← h, neg_neg, pi.neg_apply, neg'_eq]
end

lemma pfpng_ctu.add {f g : M₁ → M₂} (hf : pfpng_ctu f) (hg : pfpng_ctu g)
  (H : ∀ c₁, ∃ c₂, ∀ x : filtration M₁ c₁, f x ∈ filtration M₂ c₂) :
  pfpng_ctu (f + g) :=
begin
  intros c₁ c₂ fg₀ hfg₀,
  obtain ⟨cf, hcf⟩ := H c₁,
  let f₀ : filtration M₁ c₁ → filtration M₂ cf := λ x, ⟨f x, hcf x⟩,
  have hf₀ : ∀ x, f ↑x = f₀ x := λ x, rfl,
  have f₀_ctu : continuous f₀ := hf f₀ hf₀,
  let cg := cf + c₂,
  haveI : fact (c₂ ≤ cf + cg) :=
    calc c₂ ≤ cf + c₂        : self_le_add_left _ _
        ... ≤ cf + (cf + c₂) : self_le_add_left _ _,
  have hcg : ∀ x : filtration M₁ c₁, g x ∈ filtration M₂ cg,
  { intros x,
    have : g x = -(f x) + (f + g) x,
    { simp only [pi.add_apply, neg_add_cancel_left] },
    rw this,
    refine add_mem_filtration (neg_mem_filtration $ hcf x) _,
    rw hfg₀,
    exact (fg₀ x).2 },
  let g₀ : filtration M₁ c₁ → filtration M₂ cg := λ x, ⟨g x, hcg x⟩,
  have hg₀ : ∀ x, g ↑x = g₀ x := λ x, rfl,
  have g₀_ctu : continuous g₀ := hg g₀ hg₀,
  have aux := (f₀_ctu.prod_mk g₀_ctu),
  rw (embedding_cast_le c₂ (cf + cg)).continuous_iff,
  convert (continuous_add' cf cg).comp aux using 1,
  ext, dsimp, rw [← hfg₀, pi.add_apply]
end

variables (M)

lemma pfpng_ctu_id : pfpng_ctu (@id M) :=
begin
  intros c₁ c₂ f₀ h,
  haveI : fact (c₁ ≤ max c₁ c₂) := le_max_left _ _,
  haveI : fact (c₂ ≤ max c₁ c₂) := le_max_right _ _,
  have : @cast_le M _ c₂ (max c₁ c₂) _ ∘ f₀ = cast_le, { ext, dsimp, rw ← h, refl },
  rw [(embedding_cast_le c₂ (max c₁ c₂)).continuous_iff, this],
  exact (embedding_cast_le _ _).continuous
end

lemma pfpng_ctu_smul_nat : ∀ (n : ℕ), pfpng_ctu (λ x : M, n • x)
| 0     := pfpng_ctu_const 0
| (n+1) := (pfpng_ctu_id M).add (pfpng_ctu_smul_nat n) (λ c, ⟨c, λ x, x.2⟩)

lemma pfpng_ctu_smul_int : ∀ (n : ℤ), pfpng_ctu (λ x : M, n • x)
| (n:ℕ)  := pfpng_ctu_smul_nat M n
| -[1+n] := (pfpng_ctu_smul_nat M (n+1)).neg

end pfpng_ctu

/-- A function `f : M₁^m → M₂^n` between powers of profinitely filtered pseudo normed groups
is continuous if it is continuous when restricted to the filtration sets.

Implementation details:

* To avoid diamonds of topologies on `filtration M c` we avoid `topological_space M`.
* This definitions attempts to avoid moving between `(filtration M c)^n` and `filtration (M^n) c`.
  It is therefore particularly ad hoc. -/
def pfpng_ctu' {m n : ℕ} (f : M₁^m → M₂^n) : Prop :=
∀ ⦃c₁ c₂⦄ (f₀ : (filtration M₁ c₁ : Type*)^m → (filtration M₂ c₂ : Type*)^n)
  (h : ∀ x, f (pow_incl x) = pow_incl (f₀ x)), continuous f₀

section pfpng_ctu'

variables {m n : ℕ}

lemma pfpng_ctu'_const (y : M₂^n) : pfpng_ctu' (λ x : M₁^m, y) :=
begin
  intros c₁ c₂ f₀ h,
  suffices : f₀ = λ x, f₀ (λ i, ⟨0, zero_mem_filtration _⟩),
  { rw this, exact continuous_const },
  ext1 x,
  apply pow_incl_injective,
  rw [← h, ← h]
end

lemma pfpng_ctu'_of_pfpng_ctu (i : fin m) (f : M₁ → M₂^n) (h : ∀ j, pfpng_ctu (λ x, f x j)) :
  pfpng_ctu' (λ x, f (x i)) :=
begin
  intros c₁ c₂ f₀ h₀,
  apply continuous_pi,
  intro j,
  have aux : ∀ (x : filtration M₁ c₁), f x j ∈ filtration M₂ c₂,
  { intro x, specialize h₀ (λ i, x), dsimp at h₀, simp only [h₀, pow_incl_apply],
    exact (f₀ (λ i, x) j).2 },
  let g : filtration M₁ c₁ → filtration M₂ c₂ := λ x, ⟨f x j, aux x⟩,
  have hg : ∀ x, f₀ x j = g (x i),
  { intro x, apply subtype.coe_injective, exact (congr_fun (h₀ x) j).symm },
  simp only [hg],
  exact (h j g (λ x, rfl)).comp (continuous_apply _),
end

-- -- we don't need this
-- lemma pfpng_ctu'_iff_pfpng_ctu (i : fin m) (f : M₁ → M₂^n) :
--   pfpng_ctu' (λ x, f (x i)) ↔ (∀ j, pfpng_ctu (λ x, f x j)) :=
-- admit

lemma pfpng_ctu'.add {f g : M₁^m → M₂^n} (hf : pfpng_ctu' f) (hg : pfpng_ctu' g)
  (H : ∀ c₁, ∃ c₂, ∀ (x : (filtration M₁ c₁ : Type*)^m) j, f (pow_incl x) j ∈ filtration M₂ c₂) :
  pfpng_ctu' (f + g) :=
begin
  intros c₁ c₂ fg₀ hfg₀,
  obtain ⟨cf, hcf⟩ := H c₁,
  let f₀ : (filtration M₁ c₁ : Type*)^m → (filtration M₂ cf : Type*)^n :=
  λ x j, ⟨f (pow_incl x) j, hcf x j⟩,
  have hf₀ : ∀ x, f (pow_incl x) = pow_incl (f₀ x) := λ x, rfl,
  have f₀_ctu : continuous f₀ := hf f₀ hf₀,
  let cg := cf + c₂,
  haveI : fact (c₂ ≤ cf + cg) :=
    calc c₂ ≤ cf + c₂        : self_le_add_left _ _
        ... ≤ cf + (cf + c₂) : self_le_add_left _ _,
  have hcg : ∀ (x : (filtration M₁ c₁ : Type*)^m) j, g (pow_incl x) j ∈ filtration M₂ cg,
  { intros x j,
    have : g (pow_incl x) j = -(f (pow_incl x) j) + (f + g) (pow_incl x) j,
    { simp only [pi.add_apply, neg_add_cancel_left] },
    rw this,
    refine add_mem_filtration (neg_mem_filtration $ hcf x j) _,
    rw hfg₀,
    exact (fg₀ x j).2 },
  let g₀ : (filtration M₁ c₁ : Type*)^m → (filtration M₂ cg : Type*)^n :=
  λ x j, ⟨g (pow_incl x) j, hcg x j⟩,
  have hg₀ : ∀ x, g (pow_incl x) = pow_incl (g₀ x) := λ x, rfl,
  have g₀_ctu : continuous g₀ := hg g₀ hg₀,
  have aux := f₀_ctu.prod_mk g₀_ctu,
  apply continuous_pi,
  intro j,
  have aux' := ((continuous_apply j).prod_map (continuous_apply j)).comp aux,
  dsimp [function.comp] at aux',
  rw (embedding_cast_le c₂ (cf + cg)).continuous_iff,
  convert (continuous_add' cf cg).comp aux' using 1,
  ext x,
  replace hfg₀ := congr_fun (hfg₀ x) j,
  dsimp at hfg₀ ⊢, rw [← hfg₀], refl
end

lemma pfpng_ctu'_sum {ι : Type*} (s : finset ι)
  (f : ι → M₁^m → M₂^n) (h : ∀ i ∈ s, pfpng_ctu' (f i))
  (H : ∀ i ∈ s, ∀ c₁, ∃ c₂, ∀ (x : (filtration M₁ c₁ : Type*)^m) j, f i (pow_incl x) j ∈ filtration M₂ c₂) :
  pfpng_ctu' (∑ i in s, f i) :=
begin
  classical, revert h H,
  apply finset.induction_on s; clear s,
  { simp only [finset.sum_empty], intros, exact pfpng_ctu'_const 0 },
  intros i s his IH h H,
  simp [his, IH, h, finset.sum_insert],
  apply pfpng_ctu'.add,
  { exact h _ (finset.mem_insert_self _ _) },
  { apply IH,
    { intros i' hi', exact h _ (finset.mem_insert_of_mem hi') },
    { intros i' hi', exact H _ (finset.mem_insert_of_mem hi') } },
  { exact H _ (finset.mem_insert_self _ _) }
end

end pfpng_ctu'

end continuity
