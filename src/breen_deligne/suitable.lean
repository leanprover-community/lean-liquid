import breen_deligne.category
import data.real.nnreal

import for_mathlib.free_abelian_group
import for_mathlib.add_monoid_hom

import facts.nnreal

/-

# "suitability" of a universal map

If `f` is a universal map then a pair `(c₁, c₂)` of non-negative reals is
`f`-suitable, if (morally) `f` sends things of norm at most `c₁` to things
of norm at most `c₂`. The formal definition is in definitions 1.11 and 1.12
of the blueprint.

## Main definitions

- `breen_deligne.basic_univeral_map.suitable` :  see blueprint definition 1.11.
- `breen_deligne.universal_map.suitable` : see blueprint definition 1.12.
- `breen_deligne.data.suitable` : see blueprint definition 1.13.

These are all precise ways of controlling the norm on maps between normed
objects induced by `f`.
-/

open_locale nnreal big_operators

-- move this??
/-- `rescale_constants c_ N` for a sequence `c_ : ℕ → ℝ≥0`,
  is the sequence `(c_ i) / N`. -/
noncomputable
def rescale_constants (c_ : ℕ → ℝ≥0) (N : ℝ≥0) : ℕ → ℝ≥0 :=
λ i, (c_ i) * N⁻¹

namespace rescale_constants

@[simp] lemma one (c_ : ℕ → ℝ≥0) : rescale_constants c_ 1 = c_ :=
by { ext i, simp only [rescale_constants, mul_one, inv_one] }

end rescale_constants

namespace breen_deligne

variables {k l m n : ℕ}
variables (r r' : ℝ≥0) (S : Type*) (c c₁ c₂ c₃ c₄ : ℝ≥0) [fintype S]

namespace basic_universal_map

variables (f : basic_universal_map m n)

/-- Addition goes from `Mbar r' S c` to `Mbar r' S c_` for suitable `c_`.
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

instance suitable_id : (id n).suitable c c :=
begin
  intro i,
  calc _ ≤ 1 * c : mul_le_mul' (le_of_eq _) le_rfl
     ... = c : one_mul c,
  simp only [id, int.nat_abs],
  rw [finset.sum_eq_single i],
  { simp only [matrix.one_apply_eq, nat.cast_one, int.nat_abs_one] },
  { rintro j - hj,
    simp only [int.nat_abs_eq_zero, matrix.one_apply_ne' hj, nat.cast_eq_zero, one_ne_zero] },
  { intro h, exact (h $ finset.mem_univ _).elim }
end

-- this cannot be an instance, because c₂ cannot be inferred
lemma suitable_comp {g : basic_universal_map m n} {f : basic_universal_map l m}
  {c₁ : ℝ≥0} (c₂ : ℝ≥0) {c₃ : ℝ≥0}
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (comp g f).suitable c₁ c₃ :=
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

instance suitable_zero_left (f : basic_universal_map m n) (c : ℝ≥0) : f.suitable 0 c :=
λ j, by { rw [mul_zero], exact zero_le' }

lemma suitable.le (hf : f.suitable c₂ c₃) (h1 : c₁ ≤ c₂) (h2 : c₃ ≤ c₄) :
  f.suitable c₁ c₄ :=
λ j, (mul_le_mul' le_rfl h1).trans ((hf j).trans h2)

lemma suitable_of_le [hf : f.suitable c₂ c₃] (h1 : c₁ ≤ c₂) (h2 : c₃ ≤ c₄) :
  f.suitable c₁ c₄ :=
hf.le _ _ _ _ _ h1 h2

instance suitable_mul_left_one_le (f : basic_universal_map m n)
  [h : f.suitable c₁ c₂] [fact (1 ≤ c)] :
  f.suitable c₁ (c * c₂) :=
h.le _ _ _ _ _ le_rfl $ fact.out _

instance suitable_mul_right_one_le (f : basic_universal_map m n)
  [h : f.suitable c₁ c₂] [fact (1 ≤ c)] :
  f.suitable c₁ (c₂ * c) :=
h.le _ _ _ _ _ le_rfl $ fact.out _

instance suitable_mul_left_le_one (f : basic_universal_map m n)
  [h : f.suitable c₁ c₂] [fact (c ≤ 1)] :
  f.suitable (c * c₁) c₂ :=
h.le _ _ _ _ _ (fact.out _) le_rfl

instance suitable_mul_right_le_one (f : basic_universal_map m n)
  [h : f.suitable c₁ c₂] [fact (c ≤ 1)] :
  f.suitable (c₁ * c) c₂ :=
h.le _ _ _ _ _ (fact.out _) le_rfl

instance suitable_add (f g : basic_universal_map m n) (c cf cg : ℝ≥0)
  [hf : f.suitable c cf] [hg : g.suitable c cg] :
  (f + g).suitable c (cf + cg) :=
begin
  intro i,
  calc (∑ (j : fin m), ↑(((f + g) i j).nat_abs)) * c
      ≤ (∑ (j : fin m), ↑((f i j).nat_abs) + ∑ (j : fin m), ↑((g i j).nat_abs)) * c : _
  ... ≤ cf + cg : _,
  { rw ← finset.sum_add_distrib,
    refine mul_le_mul' (finset.sum_le_sum _) le_rfl,
    rintro j -,
    rw [← nat.cast_add, nat.cast_le],
    apply int.nat_abs_add_le, },
  { rw add_mul, apply add_le_add (hf i) (hg i) }
end

instance suitable_sum {ι : Type*} (s : finset ι) (f : ι → basic_universal_map m n)
  {c : ℝ≥0} {c' : ι → ℝ≥0}
  [hf : ∀ i, (f i).suitable c (c' i)] :
  (∑ i in s, f i).suitable c (∑ i in s, c' i) :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [finset.sum_empty], apply_instance },
  { intros i s his IH,
    simp only [finset.sum_insert his], resetI, apply_instance }
end

instance π₁_suitable (c : ℝ≥0) :
  (π₁ n).suitable c c :=
begin
  intro i,
  apply le_of_eq,
  rw [π₁, finset.sum_eq_single (fin_sum_fin_equiv (sum.inl i))],
  { simp only [matrix.reindex_linear_equiv_apply, matrix.reindex_apply, matrix.minor_apply,
      equiv.symm_apply_apply],
    dsimp [equiv.sum_empty],
    simp only [matrix.one_apply_eq, nat.cast_one, int.nat_abs_one, one_mul] },
  { rintro j - hj,
    simp only [matrix.reindex_linear_equiv_apply, equiv.symm_apply_apply],
    dsimp [equiv.sum_empty],
    generalize hj' : fin_sum_fin_equiv.symm j = j',
    cases j' with j' j',
    { dsimp,
      suffices : i ≠ j',
      { simp only [this, matrix.one_apply_ne, ne.def, not_false_iff, nat.cast_zero, int.nat_abs_zero] },
      rintro rfl, apply hj, rw [← hj', equiv.apply_symm_apply] },
    { dsimp, refl } },
  { intro h, exact (h $ finset.mem_univ _).elim }
end

instance π₂_suitable (c : ℝ≥0) :
  (π₂ n).suitable c c :=
begin
  intro i,
  apply le_of_eq,
  rw [π₂, finset.sum_eq_single (fin_sum_fin_equiv (sum.inr i))],
  { simp only [matrix.reindex_linear_equiv_apply, matrix.reindex_apply, matrix.minor_apply,
      equiv.symm_apply_apply],
    dsimp [equiv.sum_empty],
    simp only [matrix.one_apply_eq, nat.cast_one, int.nat_abs_one, one_mul] },
  { rintro j - hj,
    simp only [matrix.reindex_linear_equiv_apply, equiv.symm_apply_apply],
    dsimp [equiv.sum_empty],
    generalize hj' : fin_sum_fin_equiv.symm j = j',
    cases j' with j' j',
    { dsimp, refl },
    { dsimp,
      suffices : i ≠ j',
      { simp only [this, matrix.one_apply_ne, ne.def, not_false_iff, nat.cast_zero, int.nat_abs_zero] },
      rintro rfl, apply hj, rw [← hj', equiv.apply_symm_apply] } },
  { intro h, exact (h $ finset.mem_univ _).elim }
end
.

instance proj_suitable (N : ℕ) (k : fin N) (c : ℝ≥0) : (proj n k).suitable c c :=
begin
  intro i,
  apply le_of_eq,
  dsimp [proj, matrix.kronecker, proj_aux],
  rw [finset.sum_eq_single (fin_prod_fin_equiv (k, i))],
  { simp only [equiv.symm_apply_apply, if_pos rfl, matrix.one_apply_eq,
      nat.cast_one, int.nat_abs_one, one_mul] },
  { rintro j - hj,
    generalize hj' : fin_prod_fin_equiv.symm j = j',
    rw [equiv.symm_apply_eq] at hj', subst j,
    cases j' with a b,
    rw [matrix.one_apply, boole_mul, ← ite_and],
    simpa only [int.nat_abs_eq_zero, ite_eq_right_iff, nat.cast_eq_zero, one_ne_zero,
      equiv.apply_eq_iff_eq, prod.mk.inj_iff, ne.def, @eq_comm _ b] using hj },
  { intro h, exact (h $ finset.mem_univ _).elim }
end

instance mul_suitable (N : ℕ) (f : basic_universal_map m n) [hf : f.suitable c₁ c₂] :
  (basic_universal_map.mul N f).suitable c₁ c₂ :=
begin
  intros i,
  refine (le_of_eq _).trans (hf $ (fin_prod_fin_equiv.symm i).2),
  congr' 1,
  rw [← fin_prod_fin_equiv.sum_comp, ← finset.univ_product_univ, finset.sum_product,
    finset.sum_comm],
  apply fintype.sum_congr,
  intro j,
  dsimp [mul, matrix.kronecker],
  rw finset.sum_eq_single (fin_prod_fin_equiv.symm i).1,
  { congr' 2,
    simp only [one_mul, equiv.symm_apply_apply, matrix.one_apply_eq] },
  { rintro k - hk,
    simp only [equiv.symm_apply_apply, int.nat_abs_eq_zero, nat.cast_eq_zero, mul_eq_zero,
      matrix.one_apply_ne' hk, eq_self_iff_true, true_or] },
  { intro h, exact (h $ finset.mem_univ _).elim }
end
.

instance one_mul_hom_suitable : (one_mul_hom n).suitable c c :=
by { rw one_mul_hom_eq_proj, apply_instance }

instance mul_mul_inv_suitable (k : ℕ) : (mul_mul_inv m n k).suitable c c :=
begin
  intro i,
  calc _ ≤ 1 * c : mul_le_mul' (le_of_eq _) le_rfl
     ... = c : one_mul c,
  dsimp only [mul_mul_inv],
  simp only [matrix.reindex_linear_equiv_apply, matrix.reindex_apply, matrix.minor_apply,
    matrix.one_apply, equiv.eq_symm_apply],
  rw [finset.sum_eq_single, if_pos rfl, int.nat_abs_one, nat.cast_one],
  { rintro j - hj,
    rw [if_neg, int.nat_abs_zero, nat.cast_zero],
    exact hj.symm },
  { intro h, exact (h $ finset.mem_univ _).elim }
end

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

lemma suitable.le {f : universal_map m n} (hf : f.suitable c₂ c₃) (h1 : c₁ ≤ c₂) (h2 : c₃ ≤ c₄) :
  f.suitable c₁ c₄ :=
λ g hg, (suitable_of_mem_support f _ _ _ hg).le _ _ _ _ _ h1 h2

lemma suitable_of_le (f : universal_map m n) [hf : f.suitable c₂ c₃] (h1 : c₁ ≤ c₂) (h2 : c₃ ≤ c₄) :
  f.suitable c₁ c₄ :=
hf.le _ _ _ _ h1 h2

end universal_map

namespace basic_universal_map
open free_abelian_group

lemma suitable_of_suitable_of (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0)
  [h : universal_map.suitable c₁ c₂ (of f)] :
  f.suitable c₁ c₂ :=
h f $ by simp only [finset.mem_singleton, support_of]

end basic_universal_map

namespace universal_map
open free_abelian_group

instance suitable_of (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) [f.suitable c₁ c₂] :
  suitable c₁ c₂ (of f) :=
begin
  intros g hg,
  rw [support_of, finset.mem_singleton] at hg,
  rwa hg
end

@[simp] lemma suitable_of_iff (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (of f) ↔ f.suitable c₁ c₂ :=
⟨by {introI h, apply basic_universal_map.suitable_of_suitable_of }, by {introI h, apply_instance}⟩

instance suitable_zero : (0 : universal_map m n).suitable c₁ c₂ :=
(suitable_free_predicate c₁ c₂).zero

instance suitable_zero_left (f : universal_map m n) (c : ℝ≥0) : f.suitable 0 c :=
λ g hg, by apply_instance

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

instance suitable_sum {ι : Type*} (s : finset ι) (f : ι → universal_map m n) {c₁ c₂ : ℝ≥0}
  [hf : ∀ i, (f i).suitable c₁ c₂] :
  (∑ i in s, f i).suitable c₁ c₂ :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [finset.sum_empty], apply_instance },
  { intros i s his IH,
    simp only [finset.sum_insert his], resetI, apply_instance }
end

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

instance suitable_mul_left_one_le (f : universal_map m n)
  [h : f.suitable c₁ c₂] [fact (1 ≤ c)] :
  f.suitable c₁ (c * c₂) :=
h.le _ _ _ _ le_rfl $ fact.out _

instance suitable_mul_right_one_le (f : universal_map m n)
  [h : f.suitable c₁ c₂] [fact (1 ≤ c)] :
  f.suitable c₁ (c₂ * c) :=
h.le _ _ _ _ le_rfl $ fact.out _

instance suitable_mul_left_le_one (f : universal_map m n)
  [h : f.suitable c₁ c₂] [fact (c ≤ 1)] :
  f.suitable (c * c₁) c₂ :=
h.le _ _ _ _ (fact.out _) le_rfl

instance suitable_mul_right_le_one (f : universal_map m n)
  [h : f.suitable c₁ c₂] [fact (c ≤ 1)] :
  f.suitable (c₁ * c) c₂ :=
h.le _ _ _ _ (fact.out _) le_rfl

instance suitable_id : (id n).suitable c c :=
λ g hg, by { simp only [id, finset.mem_singleton, support_of] at hg, subst g, apply_instance }

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

instance σ_suitable (c : ℝ≥0) (n : ℕ) : (σ n).suitable (c * 2⁻¹) c :=
begin
  refine @universal_map.suitable_of _ _ _ _ _ (_root_.id _),
  have : c = c * 2⁻¹ + c * 2⁻¹,
  { rw [← mul_add], convert_to c = c * 1 using 2,
    { ext, norm_num },
    { rw mul_one } },
  conv { congr, skip, skip, rw this },
  apply basic_universal_map.suitable_add
end

instance π_suitable (c : ℝ≥0) (n : ℕ) : (π n).suitable c c :=
universal_map.suitable_add

instance sum_suitable (c : ℝ≥0) (n N : ℕ) : (sum n N).suitable (c * N⁻¹) c :=
begin
  by_cases hN : N = 0,
  { subst N, simp only [nat.cast_zero, inv_zero, mul_zero], apply_instance },
  refine @universal_map.suitable_of _ _ _ _ _ (_root_.id _),
  suffices : c = ∑ i : fin N, c * N⁻¹,
  { conv { congr, skip, skip, rw this },
    apply_instance },
  rw [finset.sum_const, finset.card_fin, nsmul_eq_mul, mul_left_comm, mul_inv_cancel, mul_one],
  exact_mod_cast hN
end

instance sum_two_suitable (c : ℝ≥0) (n : ℕ) : (sum n 2).suitable (c * 2⁻¹) c :=
by { convert universal_map.sum_suitable c n 2, norm_num }

instance proj_suitable (c : ℝ≥0) (n N : ℕ) : (proj n N).suitable c c :=
universal_map.suitable_sum _ _

instance mul_suitable (f : universal_map m n) [h : f.suitable c₁ c₂] (N : ℕ) [hN : fact (0 < N)] :
  (mul N f).suitable c₁ c₂ :=
begin
  intros g hg,
  rw [universal_map.mem_support_mul N hN.out] at hg,
  rcases hg with ⟨g, hg, rfl⟩,
  haveI := universal_map.suitable_of_mem_support f c₁ c₂ g hg,
  apply_instance
end

end universal_map

namespace data

open differential_object

/-- A sequence of nonnegative real numbers `c_ 0`, `c_ 1`, ...
is *suitable* with respect to a Breen--Deligne data `BD`,
if for all `i : ℕ`, the constants `c_ (i+1)` and `c_ i` are
suitable with respect to the universal map `BD.d (i+1) i`.

This definition ensures that we get a well-defined complex
of normed groups `LCC_Mbar_pow V S r' (c_ i) (BD.rank i)`,
induced by the maps `BD.d (i+1) i`. -/
class suitable (BD : data) (c_ : ℕ → ℝ≥0) : Prop :=
(universal_suitable : ∀ i j, (BD.d i j).suitable (c_ i) (c_ j))

attribute [instance] suitable.universal_suitable

variables (BD : data) (c_ : ℕ → ℝ≥0) [BD.suitable c_] (i j j' : ℕ)

def suitable.of_basic (H : ∀ i, (BD.d (i+1) i).suitable (c_ (i+1)) (c_ i)) : BD.suitable c_ :=
⟨λ j i, begin
  by_cases hij : coherent_indices ff j i,
  { dsimp [coherent_indices] at hij, subst j, exact H i },
  { rw BD.d_eq_zero hij, apply_instance }
end⟩

instance comp_suitable :
  (universal_map.comp (BD.d j i) (BD.d j' j)).suitable (c_ j') (c_ i) :=
universal_map.suitable.comp (c_ j)

instance suitable_mul_left (c : ℝ≥0) : BD.suitable (λ i, c * c_ i) :=
⟨λ i j, by apply_instance⟩

instance suitable_mul_right (c : ℝ≥0) : BD.suitable (λ i, c_ i * c) :=
⟨λ i j, by apply_instance⟩

instance suitable_rescale_constants (N : ℝ≥0) : BD.suitable (rescale_constants c_ N) :=
data.suitable_mul_right _ _ _

instance mul_obj_suitable (N : ℕ) [fact (0 < N)] : ((mul N).obj BD).suitable c_ :=
begin
  constructor,
  intros i j,
  dsimp [mul_obj_d],
  apply_instance
end

-- move this
instance fact_two_pow_inv_le_two_pow_inv (N : ℕ) : fact ((2 ^ N : ℝ≥0)⁻¹ ≤ (2 ^ N : ℕ)⁻¹) :=
⟨le_of_eq $ by norm_cast⟩

instance sum_suitable (i N : ℕ) (N' : ℝ≥0) [hN' : fact (N'⁻¹ ≤ N⁻¹)] :
  universal_map.suitable (rescale_constants c_ N' i) (c_ i) ((BD.sum N).f i) :=
(universal_map.sum_suitable _ _ _).le _ _ _ _ (mul_le_mul' le_rfl hN'.1) le_rfl

-- move this
instance fact_two_pow_inv_le_one (N : ℕ) : fact ((2 ^ N : ℝ≥0)⁻¹ ≤ 1) :=
⟨le_trans (data.fact_two_pow_inv_le_two_pow_inv N).1 $ fact.out _⟩

instance proj_suitable_strict (i N : ℕ) :
  universal_map.suitable c c ((BD.proj N).f i) :=
universal_map.proj_suitable _ _ _

instance proj_suitable (i N : ℕ) (N' : ℝ≥0) [fact (N'⁻¹ ≤ 1)] :
  universal_map.suitable (rescale_constants c_ N' i) (c_ i) ((BD.proj N).f i) :=
begin
  refine (universal_map.proj_suitable _ _ _).le _ _ _ _ _ le_rfl,
  dsimp [rescale_constants],
  apply fact.out,
end

instance hom_pow'_suitable_strict
  (f : (mul 2).obj BD ⟶ BD) (i : ℕ) [universal_map.suitable c c (f.f i)] :
  Π N, ((hom_pow' f N).f i).suitable c c
| 0     := by { dsimp [hom_pow'], exact universal_map.suitable_id _ }
| (N+1) :=
begin
  dsimp [hom_pow'],
  refine @universal_map.suitable.comp _ _ _ _ _ _ c _ _ (id _),
  refine @universal_map.mul_suitable _ _ _ _ _ (id _) _ _,
  apply_assumption
end

instance hom_pow'_sum_suitable (i N : ℕ) :
  ((data.hom_pow' (BD.sum 2) N).f i).suitable (c * (2 ^ N)⁻¹) c :=
begin
  induction N with N ih,
  { simp only [hom_pow', rescale_constants, pow_zero, inv_one, mul_one],
    exact universal_map.suitable_id _ },
  simp only [hom_pow', rescale_constants, pow_succ, mul_inv'] at ih ⊢, resetI,
  refine @universal_map.suitable.comp _ _ _ _ _ _ (c * 2⁻¹) _ (id _) (id _),
  { apply universal_map.sum_two_suitable },
  { rw [← mul_assoc, mul_right_comm],
    apply universal_map.mul_suitable }
end

end data

namespace universal_map

def very_suitable (f : universal_map m n) (r r' : out_param ℝ≥0) (c₁ c₂ : ℝ≥0) : Prop :=
∃ (N k : ℕ) (c_ : ℝ≥0), f.bound_by N ∧ f.suitable c₁ c_ ∧ r ^ k * N ≤ 1 ∧ c_ ≤ r' ^ k * c₂

attribute [class] very_suitable

namespace very_suitable

variables (f : universal_map m n)

instance suitable [hr' : fact (r' ≤ 1)] [hf : f.very_suitable r r' c₁ c₂] : f.suitable c₁ c₂ :=
begin
  unfreezingI { rcases hf with ⟨N, k, c_, hN, hf, hr, H⟩ },
  exact hf.le _ _ _ _ le_rfl (H.trans $ fact.out _)
end

instance mul_left (f : universal_map m n) [h : f.very_suitable r r' c₁ c₂] :
  f.very_suitable r r' (c * c₁) (c * c₂) :=
begin
  unfreezingI { rcases h with ⟨N, k, c_, hN, hf, hr, H⟩ },
  refine ⟨N, k, c * c_, hN, infer_instance, hr, _⟩,
  rw mul_left_comm,
  exact mul_le_mul' le_rfl H
end

instance mul_right (f : universal_map m n) [h : f.very_suitable r r' c₁ c₂] :
  f.very_suitable r r' (c₁ * c) (c₂ * c) :=
by { rw [mul_comm _ c, mul_comm _ c], apply universal_map.very_suitable.mul_left }

end very_suitable

end universal_map

namespace data

class very_suitable (BD : data) (r r' : out_param ℝ≥0) (c_ : ℕ → ℝ≥0) : Prop :=
(universal_very_suitable : ∀ i j, (BD.d i j).very_suitable r r' (c_ i) (c_ j))

attribute [instance] very_suitable.universal_very_suitable

namespace very_suitable

variables (BD : data) (c_ : ℕ → ℝ≥0)

instance suitable [hr' : fact (r' ≤ 1)] [h : BD.very_suitable r r' c_] :
  BD.suitable c_ :=
{ universal_suitable := λ i j, by apply_instance }

end very_suitable

end data

namespace package

section σπ

variables (BD : package) (c_ : ℕ → ℝ≥0)

instance σ_suitable (i : ℕ) :
  (BD.data.σ.f i).suitable (rescale_constants c_ 2 i) (c_ i) :=
by { dsimp [rescale_constants], apply_instance }

instance π_suitable (c : ℝ≥0) (i : ℕ) :
  (BD.data.π.f i).suitable c c :=
by { dsimp, apply_instance }

instance π_suitable' (i : ℕ) :
  (BD.data.π.f i).suitable (rescale_constants c_ 2 i) (c_ i) :=
begin
  refine universal_map.suitable.le _ _ (c_ i) _ (package.π_suitable _ _ i) _ le_rfl,
  dsimp [rescale_constants],
  rw [← div_eq_mul_inv, ← nnreal.coe_le_coe],
  exact half_le_self (c_ i).coe_nonneg,
end

end σπ

class adept (BD : out_param package) (c_ : out_param $ ℕ → ℝ≥0) (c' : ℕ → ℝ≥0) : Prop :=
(one_le : ∀ i, fact (1 ≤ c' i))
(suitable : BD.data.suitable (c' * c_)) -- do we need `very_suitable` here?
(htpy_suitable : ∀ j i, (BD.homotopy.h j i).suitable (rescale_constants c_ 2 j) (c' i * c_ i))

attribute [instance] adept.one_le adept.suitable adept.htpy_suitable

namespace adept

open category_theory

variables (BD : package) (c_ c' : ℕ → ℝ≥0) [adept BD c_ c']

instance mul_adept_suitable (N : ℕ) (f : (data.mul N).obj BD.data ⟶ BD.data) (i : ℕ) (c₁ : ℝ≥0)
  [hf : universal_map.suitable c₁ (c_ i) (f.f i)] :
  universal_map.suitable c₁ ((c' * c_) i) (f.f i) :=
begin
  refine hf.le _ _ _ _ le_rfl _,
  dsimp,
  apply fact.out
end

instance homotopy_pow'_suitable (j i : ℕ) :
  Π N, ((BD.data.homotopy_pow' BD.homotopy N).h j i).suitable
    (rescale_constants c_ (2 ^ N) j) ((c' * c_) i)
| 0     := universal_map.suitable_zero _ _
| (N+1) :=
begin
  dsimp [data.homotopy_pow'],
  refine @universal_map.suitable_add _ _ _ _ _ _ (id _) (id _),
  { refine @universal_map.suitable.comp
      _ _ _ _ _ _ (c' i * c_ i) _ _ (id _),
    refine @universal_map.mul_suitable _ _ _ _ _ (id _) _ _,
    refine (homotopy_pow'_suitable N).le _ _ _ _ _ le_rfl,
    calc rescale_constants c_ (2 ^ (N + 1)) j
        = c_ j * (2⁻¹ * (2 ^ N)⁻¹) : by simp only [rescale_constants, pow_succ, mul_inv']
    ... ≤ c_ j * (1 * (2 ^ N)⁻¹)   : mul_le_mul' le_rfl (mul_le_mul' (by norm_num) le_rfl)
    ... = c_ j * (2 ^ N)⁻¹         : by rw one_mul, },
  { refine @universal_map.suitable.comp
      _ _ _ _ _ _ (rescale_constants c_ 2 j) _ _ (id _),
    refine @universal_map.mul_suitable _ _ _ _ _ (id _) 2 ⟨zero_lt_two⟩,
    simp only [rescale_constants, pow_succ, mul_inv'],
    rw [← mul_assoc, mul_right_comm],
    exact @universal_map.suitable_mul_right _ _ _ _ _ _ _ }
end

instance homotopy_mul_suitable (j i N : ℕ) :
  ((BD.data.homotopy_mul BD.homotopy N).h j i).suitable
    (rescale_constants c_ (2 ^ N) j) ((c' * c_) i) :=
begin
  dsimp [data.homotopy_mul],
  simp only [add_zero, zero_add, neg_zero],
  refine @universal_map.suitable.comp _ _ _ _ _ _ (rescale_constants c_ (2 ^ N) j) _ _ (id _),
  generalize : (rescale_constants c_ (2 ^ N) j) = c,
  induction N with N IH,
  { dsimp [data.pow'_iso_mul, data.mul_one_iso, FreeMat.one_mul_iso],
    -- jmc: I don't understand why TC doesn't find the following instance...
    exact @universal_map.suitable_of _ _ _ _ _ (basic_universal_map.one_mul_hom_suitable _), },
  { dsimp [data.pow'_iso_mul],
    resetI,
    refine @universal_map.suitable.comp _ _ _ _ _ _ c _ (id _) (id _),
    { dsimp, apply_instance },
    { dsimp [data.mul_mul_iso, FreeMat.mul_mul_iso],
      erw [nat_iso.of_components.inv_app, FreeMat.iso_mk'_inv],
      apply_instance } }
end

end adept

end package

end breen_deligne
