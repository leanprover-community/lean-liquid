import algebra.punit_instances
import topology.algebra.group

import pseudo_normed_group.basic

import hacks_and_tricks.type_pow
import facts

/-!

# profinitely_filtered_pseudo_normed_group

The definition of a profinitely_filtered_pseudo_normed_group, and an API for this
definition.

-/
open pseudo_normed_group
open_locale nnreal big_operators

local attribute [instance] type_pow

-- move this
lemma int.induction_nonneg_or_nonpos {P : ℤ → Prop} (n : ℤ)
  (h₁ : ∀ n : ℕ, P n) (h₂ : ∀ n : ℕ, P (-n)) : P n :=
begin
  rcases le_or_lt 0 n with hn|hn,
  { lift n to ℕ using hn, exact h₁ n },
  { lift (-n) to ℕ using neg_nonneg.mpr hn.le with k hk, simpa only [hk, neg_neg] using h₂ k },
end

/-- A *complete Hausdorff filtered pseudo-normed topological group* is
* an abelian group `M` with an increasing filtration `filtration M c, c : ℝ≥0` such that
* `filtration M c` is a compact Hausdorff (or T2) space
* `M` is pseudo-normed, so `0 ∈ filtration M c`, `-(filtration M c) = filtration M c`,
  and `x₁ ∈ filtration M c₁, x₂ ∈ filtration M c₂ → (x₁ + x₂) ∈ filtration M (c₁ + c₂)`
* (bounded) addition and negation are continuous.

Morphisms are continuous and bounded homomorphisms. -/
class comphaus_filtered_pseudo_normed_group (M : Type*)
  extends pseudo_normed_group M :=
[topology : ∀ c, topological_space (filtration c)]
[t2 : ∀ c, t2_space (filtration c)]
--[td : ∀ c, totally_disconnected_space (filtration c)]
[compact : ∀ c, compact_space (filtration c)]
(continuous_add' : ∀ (c₁ c₂),
  continuous (add' : filtration c₁ × filtration c₂ → filtration (c₁ + c₂)))
(continuous_neg' : ∀ c, continuous (neg' : filtration c → filtration c))
(continuous_cast_le : ∀ (c₁ c₂) [h : fact (c₁ ≤ c₂)],
  continuous (cast_le : filtration c₁ → filtration c₂))

/-- A *profinitely filtered pseudo-normed topological group* is a *complete Hausdorff filtered
pseudo-normed topological group* with the additional requirement that
* `filtration M c` is a profinite set

Morphisms are continuous and bounded homomorphisms. -/
class profinitely_filtered_pseudo_normed_group (M : Type*)
  extends comphaus_filtered_pseudo_normed_group M :=
[td : ∀ c, totally_disconnected_space (filtration c)]

namespace comphaus_filtered_pseudo_normed_group

variables {M M₁ M₂ M₃ : Type*}
variables [comphaus_filtered_pseudo_normed_group M]
variables [comphaus_filtered_pseudo_normed_group M₁]
variables [comphaus_filtered_pseudo_normed_group M₂]
variables [comphaus_filtered_pseudo_normed_group M₃]

instance (c : ℝ≥0) : topological_space (filtration M c) := topology c
instance (c : ℝ≥0) : t2_space (filtration M c) := t2 c
--instance (c : ℝ≥0) : totally_disconnected_space (filtration M c) := td c
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

lemma continuous_add {X : Type*} [topological_space X] (c₁ c₂ : ℝ≥0)
  (f : X → filtration M c₁) (hf : continuous f)
  (g : X → filtration M c₂) (hg : continuous g) :
  continuous (λ x, ⟨f x + g x, add_mem_filtration (f x).2 (g x).2⟩ : X → filtration M (c₁ + c₂)) :=
begin
  have : continuous (λ x, (f x, g x)) := hf.prod_mk hg,
  exact (continuous_add' c₁ c₂).comp this,
end

lemma continuous_neg {X : Type*} [topological_space X] (c : ℝ≥0)
  (f : X → filtration M c) (hf : continuous f) :
  continuous (λ x, ⟨-f x, neg_mem_filtration (f x).2⟩ : X → filtration M c) :=
(continuous_neg' c).comp hf

lemma continuous_nsmul {X : Type*} [topological_space X] (n : ℕ) (c : ℝ≥0)
  (f : X → filtration M c) (hf : continuous f) :
  continuous (λ x, ⟨n • f x, nat_smul_mem_filtration n _ _ (f x).2⟩ : X → filtration M (n * c)) :=
begin
  induction n with n ih,
  { simp only [zero_smul],
    exact @continuous_const _ {x // x ∈ filtration M (↑0 * c)} _ _ ⟨0, zero_mem_filtration _⟩, },
  { simp only [nat.succ_eq_add_one, succ_nsmul'],
    haveI aux1 : fact (↑n * c ≤ n • c) := ⟨by simp only [le_refl, nsmul_eq_mul]⟩,
    haveI aux2 : fact (n • c + c ≤ ↑n.succ * c) := ⟨by simp [le_refl, nsmul_eq_mul, add_mul]⟩,
    exact (continuous_cast_le (n • c + c) ((n.succ) * c)).comp (continuous_add (n • c) c _
      ((continuous_cast_le _ _).comp ih) _ hf), }
end

lemma continuous_zsmul {X : Type*} [topological_space X] (n : ℤ) (c : ℝ≥0)
  (f : X → filtration M c) (hf : continuous f) :
  continuous (λ x, ⟨n • f x, int_smul_mem_filtration n _ _ (f x).2⟩ :
     X → filtration M (n.nat_abs * c)) :=
begin
  induction n using int.induction_nonneg_or_nonpos,
  { simp only [coe_nat_zsmul], exact continuous_nsmul n c f hf },
  { simp only [neg_smul],
    haveI : fact (↑n * c ≤ (-n : ℤ).nat_abs * c) :=
      ⟨by simp only [int.nat_abs_of_nat, int.nat_abs_neg]⟩,
    convert continuous_neg _ _ ((continuous_cast_le (n * c) ((-n : ℤ).nat_abs * c)).comp
      (continuous_nsmul n c f hf)) using 1,
    ext x,
    simp only [coe_cast_le, coe_nat_zsmul, subtype.coe_mk], }
end

end comphaus_filtered_pseudo_normed_group

namespace profinitely_filtered_pseudo_normed_group

variables {M : Type*} [profinitely_filtered_pseudo_normed_group M]

instance (c : ℝ≥0) : totally_disconnected_space (filtration M c) := td c

end profinitely_filtered_pseudo_normed_group

section
set_option old_structure_cmd true

structure comphaus_filtered_pseudo_normed_group_hom (M₁ M₂ : Type*)
  [comphaus_filtered_pseudo_normed_group M₁]
  [comphaus_filtered_pseudo_normed_group M₂]
  extends M₁ →+ M₂ :=
(bound' : ∃ C, ∀ c x, x ∈ filtration M₁ c → to_fun x ∈ filtration M₂ (C * c))
(continuous' : ∀ ⦃c₁ c₂⦄ (f₀ : filtration M₁ c₁ → filtration M₂ c₂)
  (h : ∀ x, to_fun ↑x = f₀ x), continuous f₀)

structure strict_comphaus_filtered_pseudo_normed_group_hom (M₁ M₂ : Type*)
  [comphaus_filtered_pseudo_normed_group M₁]
  [comphaus_filtered_pseudo_normed_group M₂]
  extends M₁ →+ M₂ :=
(strict' : ∀ c x, x ∈ filtration M₁ c → to_fun x ∈ filtration M₂ c)
(continuous' : ∀ c, continuous (pseudo_normed_group.level to_fun strict' c))

end

attribute [nolint doc_blame] comphaus_filtered_pseudo_normed_group_hom.mk
  comphaus_filtered_pseudo_normed_group_hom.to_add_monoid_hom

namespace comphaus_filtered_pseudo_normed_group_hom

open comphaus_filtered_pseudo_normed_group

variables {M M₁ M₂ M₃ : Type*}
variables [comphaus_filtered_pseudo_normed_group M]
variables [comphaus_filtered_pseudo_normed_group M₁]
variables [comphaus_filtered_pseudo_normed_group M₂]
variables [comphaus_filtered_pseudo_normed_group M₃]
variables (f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂)

instance : has_coe_to_fun (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) (λ _, M₁ → M₂):=
⟨comphaus_filtered_pseudo_normed_group_hom.to_fun⟩

@[simp] lemma coe_mk (f) (h₁) (h₂) (h₃) (h₄) :
  ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) = f :=
rfl

@[simp] lemma mk_to_monoid_hom (f) (h₁) (h₂) (h₃) (h₄) :
  (⟨f, h₁, h₂, h₃, h₄⟩ :
    comphaus_filtered_pseudo_normed_group_hom M₁ M₂).to_add_monoid_hom =
    ⟨f, h₁, h₂⟩ := rfl

@[simp] lemma coe_to_add_monoid_hom : ⇑f.to_add_monoid_hom = f := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sum {ι : Type*} (x : ι → M₁) (s : finset ι) :
  f (∑ i in s, x i) = ∑ i in s, f (x i) :=
f.to_add_monoid_hom.map_sum _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

@[simp] lemma map_zsmul (x) (n : ℤ) : f (n • x) = n • (f x) := f.to_add_monoid_hom.map_zsmul _ _

/-- Make a profinitely filtered pseudo-normed group hom
from a group hom and a proof that it is bounded and continuous. -/
def mk_of_bound (f : M₁ →+ M₂) (C : ℝ≥0)
  (hC : ∀ c, ∃ (H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c)),
    @continuous (filtration M₁ c) (filtration M₂ (C * c)) _ _ (λ x, ⟨f x, H x x.2⟩)) :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
{ bound' := ⟨C, λ c, (hC c).some⟩,
  continuous' := λ c₁ c₂ f₀ hf₀,
  begin
    obtain ⟨_, H⟩ := hC c₁,
    haveI : fact ((C * c₁) ≤ max (C * c₁) c₂) := ⟨le_max_left _ _⟩,
    haveI : fact (c₂ ≤ max (C * c₁) c₂) := ⟨le_max_right _ _⟩,
    rw (embedding_cast_le c₂ (max (C * c₁) c₂)).continuous_iff,
    rw (embedding_cast_le (C * c₁) (max (C * c₁) c₂)).continuous_iff at H,
    convert H using 1,
    ext, dsimp, rw ← hf₀, refl
  end,
  .. f }

  /-- Make a profinitely filtered pseudo-normed group hom
from a group hom and a proof that it is bounded and continuous. -/
def mk_of_strict (f : M₁ →+ M₂)
  (h : ∀ c, ∃ (H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ c),
    @continuous (filtration M₁ c) (filtration M₂ c) _ _ (λ x, ⟨f x, H x x.2⟩)) :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
mk_of_bound f 1 $ λ c,
begin
  obtain ⟨w, H⟩ := h c,
  refine ⟨_, _⟩,
  { simpa only [one_mul] },
  { rwa (embedding_cast_le (1 * c) c).continuous_iff, }
end

/-- Make a profinitely filtered pseudo-normed group hom
from a group hom and a proof that it is bounded and continuous. -/
noncomputable
def mk' (f : M₁ →+ M₂) (h : ∃ C, ∀ c, ∃ (H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c)),
    @continuous (filtration M₁ c) (filtration M₂ (C * c)) _ _ (λ x, ⟨f x, H x x.2⟩)) :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
mk_of_bound f h.some h.some_spec

@[simp] lemma coe_mk_of_bound (f : M₁ →+ M₂) (C) (h) : ⇑(mk_of_bound f C h) = f := rfl

@[simp] lemma coe_mk' (f : M₁ →+ M₂) (h) : ⇑(mk' f h) = f := rfl

def strict : Prop := ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ c

def bound_by (C : ℝ≥0) : Prop := ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c)

lemma strict_iff_bound_by_one : f.strict ↔ f.bound_by 1 :=
by simp only [strict, bound_by, one_mul]

variables {f}

lemma strict.bound_by_one (hf : f.strict) : f.bound_by 1 :=
f.strict_iff_bound_by_one.1 hf

lemma bound_by.strict (hf : f.bound_by 1) : f.strict :=
f.strict_iff_bound_by_one.2 hf

variables (f)

lemma bound : ∃ C, f.bound_by C := f.bound'

lemma mk_of_bound_bound_by (f : M₁ →+ M₂) (C) (h) : (mk_of_bound f C h).bound_by C :=
λ c, (h c).some

lemma mk_of_strict_strict (f : M₁ →+ M₂) (h) : (mk_of_strict f h).strict :=
λ c, (h c).some

protected lemma continuous ⦃c₁ c₂⦄ (f₀ : filtration M₁ c₁ → filtration M₂ c₂) (h : ∀ x, f ↑x = f₀ x) :
  continuous f₀ := f.continuous' f₀ h

-- /-- `f.level c` is the function `filtration M₁ c → filtration M₂ c`
-- induced by a `profinitely_filtered_pseudo_normed_group_hom M₁ M₂`. -/
-- @[simps] def level (c : ℝ≥0) (x : filtration M₁ c) : filtration M₂ c := ⟨f x, f.strict x.2⟩

-- lemma level_continuous (c : ℝ≥0) : continuous (f.level c) := f.continuous' c

variables {f g}

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance : has_zero (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
⟨mk_of_bound (0 : M₁ →+ M₂) 0 (λ c, ⟨λ _ _, zero_mem_filtration _, @continuous_const _ _ _ _ 0⟩)⟩

instance : inhabited (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) := ⟨0⟩

lemma zero_bound_by_zero : (0 : comphaus_filtered_pseudo_normed_group_hom M₁ M₂).bound_by 0 :=
mk_of_bound_bound_by _ _ _

lemma coe_inj ⦃f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂⦄ (h : (f : M₁ → M₂) = g) :
  f = g :=
by cases f; cases g; cases h; refl

/-- The identity function as `profinitely_filtered_pseudo_normed_group_hom`. -/
@[simps] def id : comphaus_filtered_pseudo_normed_group_hom M M :=
mk_of_bound (add_monoid_hom.id _) 1 $
begin
  refine λ c, ⟨_, _⟩,
  { intros, rwa one_mul },
  haveI : fact (1 * c ≤ c) := by { rw one_mul, exact ⟨le_rfl⟩ },
  rw (embedding_cast_le (1 * c) c).continuous_iff,
  convert continuous_id, ext, refl
end

/-- The composition of `profinitely_filtered_pseudo_normed_group_hom`s. -/
@[simps] noncomputable def comp
  (g : comphaus_filtered_pseudo_normed_group_hom M₂ M₃)
  (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₃ :=
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
  haveI : fact (Cg * Cf * c ≤ Cg * (Cf * c)) := by { rw mul_assoc, exact ⟨le_rfl⟩ },
  rw (embedding_cast_le (Cg * Cf * c) (Cg * (Cf * c))).continuous_iff,
  exact hg₀.comp hf₀
end

end comphaus_filtered_pseudo_normed_group_hom

namespace strict_comphaus_filtered_pseudo_normed_group_hom

open comphaus_filtered_pseudo_normed_group

variables {M M₁ M₂ M₃ : Type*}
variables [comphaus_filtered_pseudo_normed_group M]
variables [comphaus_filtered_pseudo_normed_group M₁]
variables [comphaus_filtered_pseudo_normed_group M₂]
variables [comphaus_filtered_pseudo_normed_group M₃]
variables (f g : strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂)

instance : has_coe_to_fun (strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂) (λ _, M₁ → M₂) :=
⟨strict_comphaus_filtered_pseudo_normed_group_hom.to_fun⟩

@[simp] lemma coe_mk (f) (h₁) (h₂) (h₃) (h₄) :
  ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂) = f :=
rfl

@[simp] lemma mk_to_monoid_hom (f) (h₁) (h₂) (h₃) (h₄) :
  (⟨f, h₁, h₂, h₃, h₄⟩ :
    strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂).to_add_monoid_hom =
    ⟨f, h₁, h₂⟩ := rfl

@[simp] lemma coe_to_add_monoid_hom : ⇑f.to_add_monoid_hom = f := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sum {ι : Type*} (x : ι → M₁) (s : finset ι) :
  f (∑ i in s, x i) = ∑ i in s, f (x i) :=
f.to_add_monoid_hom.map_sum _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

@[simp] lemma map_zsmul (x) (n : ℤ) : f (n • x) = n • (f x) := f.to_add_monoid_hom.map_zsmul _ _

/-- Make a strict comphaus filtered pseudo-normed group hom
from a group hom and a proof that it is bounded and continuous. -/
def mk' (f : M₁ →+ M₂)
  (h : ∀ c, ∃ (H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ c),
      @continuous (filtration M₁ c) (filtration M₂ c) _ _ (λ x, ⟨f x, H x x.2⟩)) :
  strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
{ strict' := λ c x hh, (h c).some x hh,
  continuous' := λ c, (h c).some_spec,
  ..f }

@[simp] lemma coe_mk' (f : M₁ →+ M₂) (h) : ⇑(mk' f h) = f := rfl

lemma strict ⦃c x⦄ : x ∈ filtration M₁ c → f x ∈ filtration M₂ c := f.strict' c x

def level {c} : filtration M₁ c → filtration M₂ c := pseudo_normed_group.level f f.strict c

protected lemma level_continuous (c) : continuous (pseudo_normed_group.level f f.strict c) :=
  f.continuous' _

@[simp] protected lemma level_cast_le' {c₁ c₂} (h : c₁ ≤ c₂) (x : filtration M₁ c₁) :
  (f.level (cast_le' h x)) = cast_le' h (f.level x) := rfl

@[simp] protected lemma level_zero {c} : f.level (0 : filtration M₁ c) = 0 :=
begin
  ext,
  dsimp,
  rw ← f.map_zero,
  refl,
end

@[simp] protected lemma level_neg {c} (x : filtration M₁ c) : f.level (-x) = - (f.level x) :=
begin
  ext,
  dsimp,
  erw ← f.map_neg,
  refl,
end

@[simp] protected lemma level_add {c₁ c₂} (x : filtration M₁ c₁ × filtration M₁ c₂) :
  f.level (add' x) = add' ⟨f.level x.1, f.level x.2⟩ :=
begin
  ext,
  dsimp,
  erw ← f.map_add,
  refl,
end

@[simp] lemma coe_level {c} (x : filtration M₁ c) : (f.level x : M₂) = f x := rfl

variables {f g}

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance : has_zero (strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
{ zero :=
  { strict' := λ c x h, pseudo_normed_group.zero_mem_filtration _,
    continuous' := λ c, begin
      let e : filtration M₁ c → filtration M₂ c := λ x,
        ⟨0, pseudo_normed_group.zero_mem_filtration _⟩,
      exact (continuous_const : continuous e),
    end,
    ..(0 : M₁ →+ M₂) } }

instance : inhabited (strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂) := ⟨0⟩

lemma coe_inj ⦃f g : strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂⦄
  (h : (f : M₁ → M₂) = g) : f = g :=
by cases f; cases g; cases h; refl

/-- The identity function as `profinitely_filtered_pseudo_normed_group_hom`. -/
@[simps] def id : strict_comphaus_filtered_pseudo_normed_group_hom M M :=
{ strict' := λ c x h, h,
  continuous' := λ c, begin
    convert continuous_id,
    ext, refl,
  end,
  ..(add_monoid_hom.id M) }

/-- The composition of `profinitely_filtered_pseudo_normed_group_hom`s. -/
@[simps] def comp
  (g : strict_comphaus_filtered_pseudo_normed_group_hom M₂ M₃)
  (f : strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₃ :=
{ strict' := λ c x h, g.strict $ f.strict h,
  continuous' := λ c, (g.level_continuous c).comp (f.level_continuous c),
  ..(g.to_add_monoid_hom.comp f.to_add_monoid_hom) }

@[simps]
def to_chfpsng_hom (f : strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_strict f.to_add_monoid_hom $
λ c, ⟨λ x h, f.strict h, f.level_continuous _⟩

end strict_comphaus_filtered_pseudo_normed_group_hom

namespace comphaus_filtered_pseudo_normed_group_hom

variables {M₁ M₂ : Type*}
variables [comphaus_filtered_pseudo_normed_group M₁]
variables [comphaus_filtered_pseudo_normed_group M₂]

def strict.to_schfpsng_hom {f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂}
  (h : f.strict) :
  strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
{ strict' := h,
  continuous' := λ c, f.continuous _ (λ x, rfl),
  ..f.to_add_monoid_hom }

end comphaus_filtered_pseudo_normed_group_hom

namespace punit

-- PR #8138
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

/-- Helper function for pseudo-normed groups.
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

open pseudo_normed_group comphaus_filtered_pseudo_normed_group

variables [comphaus_filtered_pseudo_normed_group M]
variables [comphaus_filtered_pseudo_normed_group M₁]
variables [comphaus_filtered_pseudo_normed_group M₂]
variables [comphaus_filtered_pseudo_normed_group M₃]

/-- A function `f : M₁ → M₂` between profinitely filtered pseudo-normed groups
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
    ⟨calc c₂ ≤ cf + c₂        : self_le_add_left _ _
         ... ≤ cf + (cf + c₂) : self_le_add_left _ _⟩,
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

lemma pfpng_ctu.sub {f g : M₁ → M₂} (hf : pfpng_ctu f) (hg : pfpng_ctu g)
  (H : ∀ c₁, ∃ c₂, ∀ x : filtration M₁ c₁, f x ∈ filtration M₂ c₂) :
  pfpng_ctu (f - g) :=
by { rw [sub_eq_add_neg], exact hf.add (hg.neg) H }

variables (M)

lemma pfpng_ctu_id : pfpng_ctu (@id M) :=
begin
  intros c₁ c₂ f₀ h,
  haveI : fact (c₁ ≤ max c₁ c₂) := ⟨le_max_left _ _⟩,
  haveI : fact (c₂ ≤ max c₁ c₂) := ⟨le_max_right _ _⟩,
  have : @cast_le M _ c₂ (max c₁ c₂) _ ∘ f₀ = cast_le, { ext, dsimp, rw ← h, refl },
  rw [(embedding_cast_le c₂ (max c₁ c₂)).continuous_iff, this],
  exact (embedding_cast_le _ _).continuous
end

lemma pfpng_ctu_smul_nat : ∀ (n : ℕ), pfpng_ctu (λ x : M, n • x)
| 0     := by { simp only [zero_smul], exact pfpng_ctu_const 0 }
| (n+1) := by { simp only [add_smul, one_smul, add_comm],
                exact (pfpng_ctu_id M).add (pfpng_ctu_smul_nat n) (λ c, ⟨c, λ x, x.2⟩) }

lemma pfpng_ctu_smul_int : ∀ (n : ℤ), pfpng_ctu (λ x : M, n • x)
| (n:ℕ)  := by simpa only [coe_nat_zsmul] using pfpng_ctu_smul_nat M n
| -[1+n] := by simpa only [zsmul_neg_succ_of_nat] using (pfpng_ctu_smul_nat M (n + 1)).neg

end pfpng_ctu

end continuity

namespace comphaus_filtered_pseudo_normed_group_hom

variables {M M₁ M₂ : Type*}
variables [comphaus_filtered_pseudo_normed_group M]
variables [comphaus_filtered_pseudo_normed_group M₁]
variables [comphaus_filtered_pseudo_normed_group M₂]

def add (f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
{ to_fun := f + g,
  bound' :=
  begin
    obtain ⟨Cf, hCf⟩ := f.bound,
    obtain ⟨Cg, hCg⟩ := g.bound,
    refine ⟨Cf + Cg, λ c x hx, _⟩,
    rw add_mul,
    apply add_mem_filtration (hCf hx) (hCg hx),
  end,
  continuous' :=
  begin
    apply pfpng_ctu.add f.continuous g.continuous,
    obtain ⟨Cf, hCf⟩ := f.bound,
    intro c₁,
    refine ⟨Cf * c₁, λ x, hCf x.2⟩,
  end,
  .. f.to_add_monoid_hom + g.to_add_monoid_hom }

def sub (f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
{ to_fun := f - g,
  bound' :=
  begin
    obtain ⟨Cf, hCf⟩ := f.bound,
    obtain ⟨Cg, hCg⟩ := g.bound,
    refine ⟨Cf + Cg, λ c x hx, _⟩,
    rw add_mul,
    apply sub_mem_filtration (hCf hx) (hCg hx),
  end,
  continuous' :=
  begin
    apply pfpng_ctu.sub f.continuous g.continuous,
    obtain ⟨Cf, hCf⟩ := f.bound,
    intro c₁,
    refine ⟨Cf * c₁, λ x, hCf x.2⟩,
  end,
  .. f.to_add_monoid_hom - g.to_add_monoid_hom }

def neg (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
{ to_fun := -f,
  bound' :=
  begin
    obtain ⟨Cf, hCf⟩ := f.bound,
    refine ⟨Cf, λ c x hx, _⟩,
    apply neg_mem_filtration (hCf hx),
  end,
  continuous' := pfpng_ctu.neg f.continuous,
  .. -f.to_add_monoid_hom }

instance : has_add (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) := ⟨add⟩

instance : has_sub (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) := ⟨sub⟩

instance : has_neg (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) := ⟨neg⟩

instance : add_comm_group (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
function.injective.add_comm_group
  comphaus_filtered_pseudo_normed_group_hom.to_add_monoid_hom
  (λ f g h, by { ext, rw add_monoid_hom.ext_iff at h, exact h x })
  rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)

@[simps]
def to_add_monoid_hom_hom : (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) →+ (M₁ →+ M₂) :=
{ to_fun := to_add_monoid_hom,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

lemma to_add_monoid_hom_hom_injective : function.injective (@to_add_monoid_hom_hom M₁ M₂ _ _) :=
λ f g h, by { ext x, exact add_monoid_hom.congr_fun h x }

lemma bound_by.add {f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂} {Cf Cg : ℝ≥0}
  (hf : f.bound_by Cf) (hg : g.bound_by Cg) :
  (f + g).bound_by (Cf + Cg) :=
λ c x hx, by { rw add_mul, exact add_mem_filtration (hf hx) (hg hx) }

@[simp] lemma add_apply (f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) (x : M₁) :
  (f + g) x = f x + g x := rfl

@[simp] lemma sum_apply {ι : Type*} (s : finset ι)
  (f : ι → comphaus_filtered_pseudo_normed_group_hom M₁ M₂) (x : M₁) :
  (∑ i in s, f i) x = ∑ i in s, (f i x) :=
begin
  classical, apply finset.induction_on s,
  { simp only [finset.sum_empty], refl },
  { intros i s his IH,
    simp only [finset.sum_insert his, add_apply, IH] }
end

lemma sum_bound_by {ι : Type*} (s : finset ι)
  (f : ι → comphaus_filtered_pseudo_normed_group_hom M₁ M₂)
  (C : ι → ℝ≥0) (hf : ∀ i ∈ s, (f i).bound_by (C i)) :
  (∑ i in s, f i).bound_by (∑ i in s, C i) :=
begin
  classical, revert hf, apply finset.induction_on s,
  { intro, simp only [finset.sum_empty], exact zero_bound_by_zero },
  { intros i s his IH hf,
    simp only [finset.sum_insert his],
    apply (hf _ (s.mem_insert_self i)).add (IH $ λ j hj, hf _ $ finset.mem_insert_of_mem hj) }
end

end comphaus_filtered_pseudo_normed_group_hom

namespace comphaus_filtered_pseudo_normed_group

/-! ## Products -/

section pi

variables {ι : Type*} (M : ι → Type*) [Π i, comphaus_filtered_pseudo_normed_group (M i)]

instance pi_topology (c : ℝ≥0) : topological_space (filtration (Π i, M i) c) :=
topological_space.induced (filtration_pi_equiv M c) $ infer_instance

@[simps apply symm_apply]
def filtration_pi_homeo (c : ℝ≥0) :
  filtration (Π i, M i) c ≃ₜ Π i, filtration (M i) c :=
{ to_fun := λ x i, ⟨x.1 i, x.2 i⟩,
  inv_fun := λ x, ⟨λ i, x i, λ i, (x i).2⟩,
  left_inv := by { rintro ⟨x, hx⟩, refl },
  right_inv := by { intro x, ext, refl },
  continuous_to_fun :=
    begin
      rw continuous_def,
      intros U hU,
      rw is_open_induced_iff,
      refine ⟨U, hU, _⟩,
      refl,
    end,
  continuous_inv_fun :=
    begin
      rw continuous_def,
      rintros s ⟨t, ht, s_eq⟩,
      simpa [← s_eq] using continuous_def.1 _ t ht,
      { rw [filtration_pi_equiv, continuous_def],
        intros U hU,
        simp only [*, equiv.coe_fn_mk, set.preimage_id',
        subtype.coe_eta, subtype.coe_mk] },
    end
    }

instance pi_t2 (c : ℝ≥0) : t2_space (filtration (Π i, M i) c) :=
begin
  have : t2_space (Π i, filtration (M i) c) := infer_instance,
  apply @embedding.t2_space _ _ _ _ this (filtration_pi_homeo M c) (filtration_pi_homeo M c).embedding,
end

/-
instance pi_td (c : ℝ≥0) : totally_disconnected_space (filtration (Π i, M i) c) :=
begin
  obtain ⟨H⟩ : totally_disconnected_space (Π i, filtration (M i) c) := infer_instance,
  rw [← homeomorph.range_coe (filtration_pi_homeo M c), ← set.image_univ] at H,
  exact ⟨embedding.is_totally_disconnected (filtration_pi_homeo M c).embedding H⟩,
end
-/

instance pi_compact (c : ℝ≥0) : compact_space (filtration (Π i, M i) c) :=
begin
  obtain ⟨H⟩ : compact_space (Π i, filtration (M i) c) := infer_instance,
  rw [← (homeomorph.compact_image (filtration_pi_homeo M c).symm), set.image_univ,
    homeomorph.range_coe] at H,
  exact ⟨H⟩,
end

def prod_pi_homeo_pi_prod [Π i, comphaus_filtered_pseudo_normed_group (M i)]
(c₁ c₂ : ℝ≥0) :
 filtration (Π i, M i) c₁ × filtration (Π i, M i) c₂ ≃ₜ Π i, (filtration (M i) c₁ × filtration (M i) c₂) :=
{ to_fun := λ x i, ⟨⟨x.1.1 i, x.1.2 i⟩, ⟨x.2.1 i, x.2.2 i⟩⟩,
  inv_fun := λ x, ⟨⟨λ i, (x i).1.1, λ i, (x i).1.2⟩, ⟨λ i, (x i).2.1, λ i, (x i).2.2⟩⟩,
  left_inv := by {rintro ⟨x, hx⟩, simp only [subtype.coe_eta, subtype.val_eq_coe]},
  right_inv := by { intro x, ext; refl},
  continuous_to_fun :=
  begin
      apply continuous_pi,
      intro i,
      apply continuous.prod_mk,
      have h₁ := (homeomorph.comp_continuous_iff (filtration_pi_homeo M c₁)).mpr continuous_fst,
      exact (continuous_apply i).comp h₁,
      have h₂ := (homeomorph.comp_continuous_iff (filtration_pi_homeo M c₂)).mpr continuous_snd,
      exact (continuous_apply i).comp h₂,
    end,
  continuous_inv_fun :=
    begin
      apply continuous.prod_mk,
      let f₁ : (Π i, (filtration (M i) c₁) × (filtration (M i) c₂)) → (filtration (Π i, M i) c₁)
        := λ x, ⟨λ (i : ι), (x i).fst.val, λ i, (x i).fst.prop⟩,
      have : continuous ((filtration_pi_homeo M c₁) ∘ f₁),
      { apply continuous_pi,
        intro i,
        dsimp [filtration_pi_homeo, f₁],
        simp only [subtype.coe_eta],
        exact continuous_fst.comp (continuous_apply i), },
      exact (homeomorph.comp_continuous_iff (filtration_pi_homeo M c₁)).mp this,
      let f₂ : (Π i, (filtration (M i) c₁) × (filtration (M i) c₂)) → (filtration (Π i, M i) c₂)
        := λ x, ⟨λ (i : ι), (x i).snd.val, λ i, (x i).snd.prop⟩,
      have : continuous ((filtration_pi_homeo M c₂) ∘ f₂),
      { apply continuous_pi,
        intro i,
        dsimp [filtration_pi_homeo, f₂],
        simp only [subtype.coe_eta],
        exact continuous_snd.comp (continuous_apply i), },
      exact (homeomorph.comp_continuous_iff (filtration_pi_homeo M c₂)).mp this,
    end,}


instance pi : comphaus_filtered_pseudo_normed_group (Π i, M i) :=
{ continuous_add' :=
    begin
      intros c₁ c₂,
      rw [← homeomorph.comp_continuous_iff (filtration_pi_homeo M (c₁ + c₂)),
        ← homeomorph.comp_continuous_iff' (prod_pi_homeo_pi_prod M c₁ c₂).symm],
      apply continuous_pi,
      intro i,
      exact (continuous_add' c₁ c₂).comp (continuous_apply i),
    end,
  continuous_neg' :=
    begin
      intro c,
      rw [← homeomorph.comp_continuous_iff (filtration_pi_homeo M c),
        ← homeomorph.comp_continuous_iff' (filtration_pi_homeo M c).symm],
      apply continuous_pi,
      intro i,
      exact (continuous_neg' c).comp (continuous_apply i),
    end,
  continuous_cast_le :=
    begin
      intros c₁ c₂ h,
      rw [← homeomorph.comp_continuous_iff (filtration_pi_homeo M c₂),
        ← homeomorph.comp_continuous_iff' (filtration_pi_homeo M c₁).symm],
      apply continuous_pi,
      intro i,
      have := @continuous_cast_le _ _ _ _ h,
      exact this.comp (continuous_apply i),
    end,
  .. pseudo_normed_group.pi M }

variables {M}

@[simps]
def pi_proj (i : ι) : comphaus_filtered_pseudo_normed_group_hom (Π i, M i) (M i) :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_bound (pi.eval_add_monoid_hom M i) 1 $
begin
  refine λ c, ⟨λ x hx, by { rw one_mul, exact hx i }, _⟩,
  have := ((continuous_apply i).comp (filtration_pi_homeo M c).continuous),
  haveI : fact (c ≤ 1 * c) := by { rw one_mul, exact ⟨le_rfl⟩ },
  rw (embedding_cast_le c (1 * c)).continuous_iff at this,
  convert this using 0,
end

lemma pi_proj_bound_by (i : ι) : (@pi_proj _ M _ i).bound_by 1 :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ _ _

/-- Universal property of the product of profinitely filtered pseudo-normed groups -/
@[simps {fully_applied := ff}]
def pi_lift {N : Type*} [comphaus_filtered_pseudo_normed_group N]
  (f : Π i, comphaus_filtered_pseudo_normed_group_hom N (M i))
  (hf : ∃ C, ∀ i, (f i).bound_by C) :
  comphaus_filtered_pseudo_normed_group_hom N (Π i, M i) :=
{ to_fun := add_monoid_hom.mk_to_pi (λ i, (f i).to_add_monoid_hom),
  bound' := by { obtain ⟨C, hC⟩ := hf, refine ⟨C, λ c x hx i, hC i hx⟩ },
  continuous' :=
  begin
    intros c₁ c₂ f₀ hf₀,
    apply continuous_induced_rng,
    apply continuous_pi,
    intro i,
    let g := function.eval i ∘ filtration_pi_homeo M c₂ ∘ f₀,
    refine (f i).continuous g (λ x, _),
    specialize hf₀ x, rw function.funext_iff at hf₀,
    exact hf₀ i
  end,
  .. add_monoid_hom.mk_to_pi (λ i, (f i).to_add_monoid_hom) }

noncomputable def pi_map {N : ι → Type*} [Π i, comphaus_filtered_pseudo_normed_group (N i)]
  (f : Π i, comphaus_filtered_pseudo_normed_group_hom (M i) (N i))
  (hf : ∃ C, ∀ i, (f i).bound_by C) :
  comphaus_filtered_pseudo_normed_group_hom (Π i, M i) (Π i, N i) :=
pi_lift (λ i, (f i).comp (pi_proj i))
begin
  obtain ⟨C, hC⟩ := hf,
  refine ⟨C, λ i c x hx, hC i _⟩,
  have := pi_proj_bound_by i hx,
  rwa one_mul at this,
end

end pi

end comphaus_filtered_pseudo_normed_group

namespace profinitely_filtered_pseudo_normed_group

/-! ## Products -/

section pi

open comphaus_filtered_pseudo_normed_group

variables {ι : Type*} (M : ι → Type*) [Π i, profinitely_filtered_pseudo_normed_group (M i)]

instance pi_td (c : ℝ≥0) : totally_disconnected_space (filtration (Π i, M i) c) :=
begin
  obtain ⟨H⟩ : totally_disconnected_space (Π i, filtration (M i) c) := infer_instance,
  rw [← homeomorph.range_coe (filtration_pi_homeo M c), ← set.image_univ] at H,
  exact ⟨embedding.is_totally_disconnected (filtration_pi_homeo M c).embedding H⟩,
end

instance pi : profinitely_filtered_pseudo_normed_group (Π i, M i) :=
{ ..(infer_instance : comphaus_filtered_pseudo_normed_group _) }

end pi

end profinitely_filtered_pseudo_normed_group
