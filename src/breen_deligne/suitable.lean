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

instance suitable_mul_left (f : basic_universal_map m n) [h : f.suitable c₁ c₂] :
  f.suitable (c * c₁) (c * c₂) :=
λ i, by { rw mul_left_comm, exact mul_le_mul' le_rfl (h i) }

instance suitable_mul_right (f : basic_universal_map m n) [h : f.suitable c₁ c₂] :
  f.suitable (c₁ * c) (c₂ * c) :=
by { rw [mul_comm _ c, mul_comm _ c], exact basic_universal_map.suitable_mul_left _ _ _ _ }

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

instance suitable_sub {f g : universal_map m n} {c₁ c₂ : ℝ≥0}
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₁ c₂] :
  suitable c₁ c₂ (f - g) :=
by rw sub_eq_add_neg; apply_instance

lemma suitable_smul_iff (k : ℤ) (hk : k ≠ 0) (f : universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (k • f) ↔ f.suitable c₁ c₂ :=
(suitable_free_predicate c₁ c₂).smul_iff k hk

instance suitable_mul_left (f : universal_map m n) [h : f.suitable c₁ c₂] :
  f.suitable (c * c₁) (c * c₂) :=
λ g hg, @basic_universal_map.suitable_mul_left _ _ _ _ _ _ (h g hg)

instance suitable_mul_right (f : universal_map m n) [h : f.suitable c₁ c₂] :
  f.suitable (c₁ * c) (c₂ * c) :=
by { rw [mul_comm _ c, mul_comm _ c], exact universal_map.suitable_mul_left _ _ _ _ }

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

namespace data

open differential_object

/-- A sequence of nonnegative real numbers `c' 0`, `c' 1`, ...
is *suitable* with respect to a Breen--Deligne data `BD`,
if for all `i : ℕ`, the constants `c' (i+1)` and `c' i` are
suitable with respect to the universal map `BD.d (i+1) i`.

This definition ensures that we get a well-defined complex
of normed groups `LCC_Mbar_pow V S r' (c' i) (BD.rank i)`,
induced by the maps `BD.d (i+1) i`. -/
class suitable (BD : data) (c' : ℕ → ℝ≥0) : Prop :=
(universal_suitable : ∀ i j, (BD.d i j).suitable (c' i) (c' j))

attribute [instance] suitable.universal_suitable

variables (BD : data) (c' : ℕ → ℝ≥0) [BD.suitable c'] (i j j' : ℕ)

def suitable.of_basic (H : ∀ i, (BD.d (i+1) i).suitable (c' (i+1)) (c' i)) : BD.suitable c' :=
⟨λ j i, begin
  by_cases hij : coherent_indices ff j i,
  { dsimp [coherent_indices] at hij, subst j, exact H i },
  { rw BD.d_eq_zero hij, apply_instance }
end⟩

instance comp_suitable :
  (universal_map.comp (BD.d j i) (BD.d j' j)).suitable (c' j') (c' i) :=
universal_map.suitable.comp (c' j)

instance suitable_mul_left (c : ℝ≥0) :
  BD.suitable (λ i, c * c' i) :=
⟨λ i j, by apply_instance⟩

instance suitable_mul_right (c : ℝ≥0) :
  BD.suitable (λ i, c' i * c) :=
⟨λ i j, by apply_instance⟩

end data

section double

instance basic_universal_map.double_suitable (f : basic_universal_map m n) [f.suitable c₁ c₂] :
  (basic_universal_map.double f).suitable c₁ c₂ :=
begin
  intros i,
  -- now use that `double` is a block matrix, so every row/column is just a row/column of `f`
  -- with a whole bunch of extra `0`s
  sorry
end

-- move this
lemma universal_map.mem_support_double (f : universal_map m n) (g) :
  g ∈ (universal_map.double f).support ↔ ∃ g', g' ∈ f.support ∧ g = basic_universal_map.double g' :=
sorry

instance universal_map.double_suitable (f : universal_map m n) [f.suitable c₁ c₂] :
  (universal_map.double f).suitable c₁ c₂ :=
begin
  intros g hg,
  simp only [data.double_d, universal_map.mem_support_double] at hg,
  rcases hg with ⟨g, hg, rfl⟩,
  haveI := universal_map.suitable_of_mem_support f c₁ c₂ g hg,
  apply_instance
end

instance data.double_suitable (BD : data) (c' : ℕ → ℝ≥0) [BD.suitable c'] :
  BD.double.suitable c' :=
{ universal_suitable := λ i j, universal_map.double_suitable _ _ _ }

instance data.pow_suitable  (BD : data) (c' : ℕ → ℝ≥0) [BD.suitable c'] :
  ∀ N, (BD.pow N).suitable c'
| 0     := sorry
| (N+1) := sorry

end double

-- move this??
noncomputable
def rescale_constants (c' : ℕ → ℝ≥0) (N : ℝ≥0) : ℕ → ℝ≥0 :=
λ i, (c' i) * N⁻¹

section σπ

variables (BD : package) (c' : ℕ → ℝ≥0)

instance σ_suitable (i : ℕ) :
  (BD.data.σ.f i).suitable (c' i) (rescale_constants c' 2 i) :=
sorry

instance π_suitable (i : ℕ) :
  (BD.data.π.f i).suitable (c' i) (c' i) :=
sorry

instance σ_suitable' (k' : ℝ≥0) (N : ℕ) [fact (1 ≤ k')] [fact (k' ≤ 2^N)] (i : ℕ) :
  ((data.hom_pow BD.data.σ N).f i).suitable (c' i) (k' * rescale_constants c' 2 i) :=
sorry

instance π_suitable' (k' : ℝ≥0) (N : ℕ) [fact (1 ≤ k')] [fact (k' ≤ 2^N)] (i : ℕ) :
  ((data.hom_pow BD.data.π N).f i).suitable (c' i) (k' * rescale_constants c' 2 i) :=
sorry

end σπ

end breen_deligne
