import algebra.punit_instances
import topology.algebra.group

import pseudo_normed_group.basic

open pseudo_normed_group
open_locale nnreal big_operators

-- /-- A *profinitely filtered pseudo normed topological group* is
-- * an abelian group `M` with an increasing filtration `filtration M c, c : ℝ≥0` such that
-- * `filtration M c` is a profinite set
-- * `M` is pseudo normed, so `0 ∈ filtration M c`, `-(filtration M c = filtration M c`,
--   and `x₁ ∈ filtration M c₁, x₂ ∈ filtration M c₂ → (x₁ + x₂) ∈ filtration M (c₁ + c₂)`
-- * (bounded) addition and negation are continuous.

-- Morphisms are continuous and bounded homomorphisms. -/
-- class profinitely_filtered_pseudo_normed_group' (M : Type*)
--   [pseudo_normed_group M] [topological_space M] extends topological_add_group M :=
-- [to_t2_space : t2_space M]
-- [to_totally_disconnected_space : totally_disconnected_space M]
-- (is_compact : ∀ c, is_compact (filtration M c))

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
(add' : Π {c₁ c₂}, (filtration c₁) × (filtration c₂) → (filtration (c₁ + c₂)))
(add'_eq : ∀ {c₁ c₂ : ℝ≥0} (x : (filtration c₁) × (filtration c₂)), (add' x : M) = x.1 + x.2)
(continuous_add' : Π (c₁ c₂), continuous (@add' c₁ c₂))
(neg' : Π {c}, (filtration c) → (filtration c))
(neg'_eq : ∀ {c : ℝ≥0} (x : filtration c), (neg' x : M) = -x)
(continuous_neg' : Π c, continuous (@neg' c))
(cast_le_open_map : ∀ (c₁ c₂) [h : fact (c₁ ≤ c₂)],
  is_open_map (@pseudo_normed_group.cast_le M _ _ _ h))

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

end profinitely_filtered_pseudo_normed_group

section
set_option old_structure_cmd true

structure profinitely_filtered_pseudo_normed_group_hom
  (M₁ M₂ : Type*)
  [profinitely_filtered_pseudo_normed_group M₁]
  [profinitely_filtered_pseudo_normed_group M₂]
  extends M₁ →+ M₂ :=
(strict' : ∀ c x, x ∈ filtration M₁ c → to_fun x ∈ filtration M₂ c)
(continuous' : ∀ c, @continuous (filtration M₁ c) (filtration M₂ c) _ _
  $ λ x, ⟨to_fun x, strict' c x x.2⟩)

end

attribute [nolint doc_blame] profinitely_filtered_pseudo_normed_group_hom.mk
  profinitely_filtered_pseudo_normed_group_hom.to_add_monoid_hom

namespace profinitely_filtered_pseudo_normed_group_hom

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
from a group hom and proofs that it is strict and continuous. -/
def mk' (f : M₁ →+ M₂) (h : ∀ c x, x ∈ filtration M₁ c → f x ∈ filtration M₂ c)
  (h' : ∀ c, @continuous (filtration M₁ c) (filtration M₂ c) _ _ $ λ x, ⟨f x, h c x x.2⟩) :
  profinitely_filtered_pseudo_normed_group_hom M₁ M₂ :=
{ strict' := h, continuous' := h', .. f}

@[simp] lemma coe_mk' (f : M₁ →+ M₂) (h) (h') : ⇑(mk' f h h') = f := rfl

lemma strict {c : ℝ≥0} {x : M₁} (h : x ∈ filtration M₁ c) : f x ∈ filtration M₂ c :=
f.strict' c x h

/-- `f.level c` is the function `filtration M₁ c → filtration M₂ c`
induced by a `profinitely_filtered_pseudo_normed_group_hom M₁ M₂`. -/
@[simps] def level (c : ℝ≥0) (x : filtration M₁ c) : filtration M₂ c := ⟨f x, f.strict x.2⟩

lemma level_continuous (c : ℝ≥0) : continuous (f.level c) := f.continuous' c

variables {f g}

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance : has_zero (profinitely_filtered_pseudo_normed_group_hom M₁ M₂) :=
⟨{ strict' := λ c x h, zero_mem_filtration c,
   continuous' := λ c, @continuous_const _ (filtration M₂ c) _ _ ⟨0, zero_mem_filtration c⟩,
   .. (0 : M₁ →+ M₂) }⟩

instance : inhabited (profinitely_filtered_pseudo_normed_group_hom M₁ M₂) := ⟨0⟩

lemma coe_inj ⦃f g : profinitely_filtered_pseudo_normed_group_hom M₁ M₂⦄ (h : (f : M₁ → M₂) = g) : f = g :=
by cases f; cases g; cases h; refl

/-- The identity function as `profinitely_filtered_pseudo_normed_group_hom`. -/
@[simps] def id : profinitely_filtered_pseudo_normed_group_hom M M :=
{ strict' := λ c x, id,
  continuous' := λ c, by { convert continuous_id, ext, refl },
  .. add_monoid_hom.id _ }

/-- The composition of `profinitely_filtered_pseudo_normed_group_hom`s. -/
@[simps] def comp
  (g : profinitely_filtered_pseudo_normed_group_hom M₂ M₃)
  (f : profinitely_filtered_pseudo_normed_group_hom M₁ M₂) :
  profinitely_filtered_pseudo_normed_group_hom M₁ M₃ :=
{ strict' := λ c x hxc, g.strict (f.strict hxc),
  continuous' := λ c, (g.level_continuous c).comp (f.level_continuous c),
  .. g.to_add_monoid_hom.comp f.to_add_monoid_hom }

end profinitely_filtered_pseudo_normed_group_hom

namespace punit

-- move this
instance : topological_space punit := ⊥

instance : profinitely_filtered_pseudo_normed_group punit :=
{ filtration := λ _, set.univ,
  filtration_mono := λ _ _ _, set.subset_univ _,
  zero_mem_filtration := λ _, set.mem_univ _,
  neg_mem_filtration := λ _ _ _, set.mem_univ _,
  add_mem_filtration := λ _ _ _ _ _ _, set.mem_univ _,
  add' := λ _ _ _, ⟨punit.star, set.mem_univ _⟩,
  add'_eq := λ _ _ _, dec_trivial,
  continuous_add' := λ _ _, continuous_const,
  neg' := λ _ _, ⟨punit.star, set.mem_univ _⟩,
  neg'_eq := λ _ _, dec_trivial,
  continuous_neg' := λ _, continuous_const,
  cast_le_open_map := λ c₁ c₂ h s hs, is_open_discrete _ }

end punit

namespace profinitely_filtered_pseudo_normed_group

end profinitely_filtered_pseudo_normed_group
