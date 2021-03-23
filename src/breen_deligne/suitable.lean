import breen_deligne.category
import data.real.nnreal

import for_mathlib.free_abelian_group
import for_mathlib.add_monoid_hom

open_locale nnreal big_operators

namespace breen_deligne

variables {k l m n : ℕ}
variables (r' : ℝ≥0) (S : Type*) (c c₁ c₂ c₃ : ℝ≥0) [fintype S]

namespace basic_universal_map

variables (f : basic_universal_map m n)

/-- Addition goes from `Mbar r' S c` to `Mbar r' S c'` for suitable `c'`.
This predicate says what *suitable* means for basic universal maps.
See Lemma 9.11 of [Analytic]. -/
def suitable (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) : Prop :=
∀ i, (∑ j, ↑(f i j).nat_abs) * c₁ ≤ c₂

attribute [class] suitable

lemma sup_mul_le (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) [h : f.suitable c₁ c₂] :
  (finset.univ.sup $ λ i, ∑ j, ↑(f i j).nat_abs) * c₁ ≤ c₂ :=
begin
  by_cases H : c₁ = 0,
  { unfreezingI {subst H}, rw mul_zero, exact zero_le' },
  rw [mul_comm, nnreal.mul_le_iff_le_inv H, finset.sup_le_iff],
  rintro i -,
  rw [← nnreal.mul_le_iff_le_inv H, mul_comm],
  apply h
end

instance suitable_of_mul_left (f : basic_universal_map m n) [h : f.suitable c₁ c₂] :
  f.suitable (c * c₁) (c * c₂) :=
λ i, by { rw mul_left_comm, exact mul_le_mul' le_rfl (h i) }

-- move this
lemma nat_abs_sum_le_sum_nat_abs {ι : Type*} (s : finset ι) (f : ι → ℤ) :
  (∑ i in s, f i).nat_abs ≤ ∑ i in s, (f i).nat_abs :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [finset.sum_empty, int.nat_abs_zero] },
  { intros i s his IH,
    simp only [his, finset.sum_insert, not_false_iff],
    exact (int.nat_abs_add_le _ _).trans (add_le_add le_rfl IH) }
end

-- this cannot be an instance, because c₂ cannot be inferred
lemma suitable_comp {g : basic_universal_map m n} {f : basic_universal_map l m}
  {c₁ : ℝ≥0} (c₂ : ℝ≥0) {c₃ : ℝ≥0}
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (g.comp f).suitable c₁ c₃ :=
begin
  intro i,
  simp only [← nat.coe_cast_ring_hom, ← ring_hom.map_sum, comp, matrix.mul_apply],
  calc  ↑(∑ k, (∑ j, g i j * f j k).nat_abs) * c₁
      ≤ ↑(∑ j, (g i j).nat_abs * ∑ k, (f j k).nat_abs) * c₁    : _ -- proof below
  ... = ∑ j, ↑(g i j).nat_abs * ((∑ k, ↑(f j k).nat_abs) * c₁) : _ -- proof below
  ... ≤ ∑ j, ↑(g i j).nat_abs * c₂                             : _ -- proof below
  ... ≤ c₃                                                 : by { rw ← finset.sum_mul, exact hg i },
  { refine mul_le_mul' _ le_rfl,
    rw nat.cast_le,
    simp only [finset.mul_sum],
    rw finset.sum_comm,
    apply finset.sum_le_sum,
    rintro k -,
    simp only [← int.nat_abs_mul],
    apply nat_abs_sum_le_sum_nat_abs },
  { simp only [← nat.coe_cast_ring_hom, ring_hom.map_sum, ring_hom.map_mul,
      finset.sum_mul, mul_assoc] },
  { apply finset.sum_le_sum, rintro j -, exact mul_le_mul' le_rfl (hf j) }
end

@[priority 1001]
instance zero_suitable : (0 : basic_universal_map m n).suitable c₁ c₂ :=
λ i, by simp only [nat.cast_zero, zero_mul, zero_le', finset.sum_const_zero,
          matrix.zero_apply, int.nat_abs_zero]

end basic_universal_map

namespace universal_map

open free_abelian_group

/-- A univeral map `f` is `suitable c₁ c₂` if all of the matrices `g`
occuring in the formal sum `f` satisfy `g.suitable c₁ c₂`.
This definition is tailored in such a way that we get a sensible
`(LCC_Mbar_pow V S r' c₂ n) ⟶ (LCC_Mbar_pow V S r' c₁ m)`
if `f.suitable c₁ c₂`.

See Lemma 9.11 of [Analytic]. -/
def suitable (c₁ c₂ : ℝ≥0) (f : universal_map m n) : Prop :=
∀ g ∈ f.support, basic_universal_map.suitable g c₁ c₂

attribute [class] suitable

lemma suitable_of_mem_support (f : universal_map m n) (c₁ c₂ : ℝ≥0)
  (g : basic_universal_map m n) (hg : g ∈ f.support) [h : f.suitable c₁ c₂] :
  g.suitable c₁ c₂ :=
h g hg

lemma suitable_free_predicate (c₁ c₂ : ℝ≥0) :
  free_predicate (@suitable m n c₁ c₂) :=
by { intro x, simp only [suitable, forall_eq, finset.mem_singleton, support_of] }

lemma suitable_congr (f g : universal_map m n) (c₁ c₂ : ℝ≥0) (h : f = g) :
  f.suitable c₁ c₂ ↔ g.suitable c₁ c₂ :=
by subst h

end universal_map

namespace basic_universal_map
open free_abelian_group

instance suitable_of (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) [f.suitable c₁ c₂] :
  universal_map.suitable c₁ c₂ (of f) :=
begin
  intros g hg,
  rw [support_of, finset.mem_singleton] at hg,
  rwa hg
end

instance suitable_of_suitable_of (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0)
  [h : universal_map.suitable c₁ c₂ (of f)] :
  f.suitable c₁ c₂ :=
h f $ by simp only [finset.mem_singleton, support_of]

end basic_universal_map

namespace universal_map
open free_abelian_group

@[simp] lemma suitable_of_iff (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (of f) ↔ f.suitable c₁ c₂ :=
⟨by {introI h, apply_instance}, by {introI h, apply_instance}⟩

instance suitable_zero : (0 : universal_map m n).suitable c₁ c₂ :=
(suitable_free_predicate c₁ c₂).zero

instance suitable_neg (f : universal_map m n) (c₁ c₂ : ℝ≥0) [h : f.suitable c₁ c₂] :
  suitable c₁ c₂ (-f) :=
(suitable_free_predicate c₁ c₂).neg h

@[simp] lemma suitable_neg_iff (f : universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (-f) ↔ f.suitable c₁ c₂ :=
(suitable_free_predicate c₁ c₂).neg_iff

instance suitable_add {f g : universal_map m n} {c₁ c₂ : ℝ≥0}
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₁ c₂] :
  suitable c₁ c₂ (f + g) :=
(suitable_free_predicate c₁ c₂).add hf hg

lemma suitable_smul_iff (k : ℤ) (hk : k ≠ 0) (f : universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (k • f) ↔ f.suitable c₁ c₂ :=
(suitable_free_predicate c₁ c₂).smul_iff k hk

instance suitable_of_mul_left (f : universal_map m n) [h : f.suitable c₁ c₂] :
  f.suitable (c * c₁) (c * c₂) :=
λ g hg, @basic_universal_map.suitable_of_mul_left _ _ _ _ _ _ (h g hg)

-- this cannot be an instance, because c₂ cannot be inferred
lemma suitable.comp {g : universal_map m n} {f : universal_map l m} {c₁ : ℝ≥0} (c₂ : ℝ≥0)
  {c₃ : ℝ≥0} [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (comp g f).suitable c₁ c₃ :=
begin
  apply free_abelian_group.induction_on_free_predicate
    (suitable c₂ c₃) (suitable_free_predicate c₂ c₃) g hg; unfreezingI { clear_dependent g },
  { simpa only [pi.zero_apply, add_monoid_hom.coe_zero, add_monoid_hom.map_zero]
      using breen_deligne.universal_map.suitable_zero _ _ },
  { intros g hg,
    apply free_abelian_group.induction_on_free_predicate
      (suitable c₁ c₂) (suitable_free_predicate c₁ c₂) f hf; unfreezingI { clear_dependent f },
      { simp only [add_monoid_hom.map_zero], apply_instance },
      { intros f hf,
        rw comp_of,
        rw suitable_of_iff at hf hg ⊢,
        resetI,
        exact breen_deligne.basic_universal_map.suitable_comp c₂ },
      { intros g hg H, simpa only [add_monoid_hom.map_neg, suitable_neg_iff] },
      { intros g₁ g₂ hg₁ hg₂ H₁ H₂,
        simp only [add_monoid_hom.map_add],
        resetI, apply_instance } },
  { intros f hf H,
    simpa only [pi.neg_apply, add_monoid_hom.map_neg, suitable_neg_iff, add_monoid_hom.coe_neg] },
  { intros f₁ f₂ hf₁ hf₂ H₁ H₂,
    simp only [add_monoid_hom.coe_add, add_monoid_hom.map_add, pi.add_apply],
    resetI, apply_instance }
end

end universal_map

namespace package

/-- A sequence of nonnegative real numbers `c' 0`, `c' 1`, ...
is *suitable* with respect to a Breen--Deligne package `BD`,
if for all `i : ℕ`, the constants `c' (i+1)` and `c' i` are
suitable with respect to the universal map `BD.map i`.

This definition ensures that we get a well-defined complex
of normed groups `LCC_Mbar_pow V S r' (c' i) (BD.rank i)`,
induced by the maps `BD.map i`. -/
class suitable (BD : package) (c' : ℕ → ℝ≥0) : Prop :=
(universal_suitable : ∀ i, (BD.map i).suitable (c' (i+1)) (c' i))

variables (BD : package) (c' : ℕ → ℝ≥0) (i : ℕ) [BD.suitable c']

instance basic_suitable_of_suitable : ((BD.map i).suitable (c' (i+1)) (c' i)) :=
suitable.universal_suitable i

instance suitable_of_suitable :
  ((universal_map.comp (BD.map i) (BD.map (i+1))).suitable (c' (i+2)) (c' i)) :=
universal_map.suitable.comp (c' (i + 1))

end package

end breen_deligne
