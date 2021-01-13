import group_theory.free_abelian_group
import data.finsupp.basic

noncomputable theory

open_locale big_operators

namespace int

variables {A : Type*} [add_comm_group A]

def cast_add_hom' (a : A) : ℤ →+ A :=
add_monoid_hom.mk' (λ n, n • a) $ λ m n, add_smul _ _ _

@[simp] lemma cast_add_hom'_apply (a : A) (n : ℤ) : cast_add_hom' a n = n • a := rfl

end int

namespace free_abelian_group
variables (X : Type*)

def to_finsupp : free_abelian_group X →+ (X →₀ ℤ) :=
free_abelian_group.lift $ λ x, finsupp.single x 1

def from_finsupp : (X →₀ ℤ) →+ free_abelian_group X :=
finsupp.lift_add_hom $ λ x, @int.cast_add_hom' (free_abelian_group X) _ (of x)

@[simp] lemma from_finsupp_comp_single_add_hom (x : X) :
  (from_finsupp X).comp (finsupp.single_add_hom x) =
    @int.cast_add_hom' (free_abelian_group X) _ (of x) :=
begin
  ext,
  simp only [add_monoid_hom.coe_comp, finsupp.single_add_hom_apply, function.comp_app,
    one_smul, int.cast_add_hom'_apply, from_finsupp, finsupp.lift_add_hom_apply_single]
end

@[simp] lemma to_finsupp_comp_from_finsupp :
  (to_finsupp X).comp (from_finsupp X) = add_monoid_hom.id _ :=
begin
  ext x y, simp only [add_monoid_hom.id_comp],
  rw [add_monoid_hom.comp_assoc, from_finsupp_comp_single_add_hom],
  simp only [to_finsupp, add_monoid_hom.coe_comp, finsupp.single_add_hom_apply,
    function.comp_app, one_smul, lift.of, int.cast_add_hom'_apply],
end

@[simp] lemma from_finsupp_comp_to_finsupp :
  (from_finsupp X).comp (to_finsupp X) = add_monoid_hom.id _ :=
begin
  ext,
  simp only [from_finsupp, to_finsupp, finsupp.lift_add_hom_apply_single, add_monoid_hom.coe_comp,
    function.comp_app, one_smul, add_monoid_hom.id_apply, lift.of, int.cast_add_hom'_apply]
end

variable {X}

@[simp] lemma to_finsupp_of (x : X) :
  to_finsupp X (of x) = finsupp.single x 1 :=
by simp only [to_finsupp, lift.of]

@[simp] lemma to_finsupp_from_finsupp (f) :
  (to_finsupp X) (from_finsupp X f) = f :=
by rw [← add_monoid_hom.comp_apply, to_finsupp_comp_from_finsupp, add_monoid_hom.id_apply]

@[simp] lemma from_finsupp_to_finsupp (x) :
  (from_finsupp X) (to_finsupp X x) = x :=
by rw [← add_monoid_hom.comp_apply, from_finsupp_comp_to_finsupp, add_monoid_hom.id_apply]

variable (X)

@[simps]
def equiv_finsupp : free_abelian_group X ≃+ (X →₀ ℤ) :=
{ to_fun := to_finsupp X,
  inv_fun := from_finsupp X,
  left_inv := from_finsupp_to_finsupp,
  right_inv := to_finsupp_from_finsupp,
  map_add' := (to_finsupp X).map_add }

variable {X}

def coeff (x : X) : free_abelian_group X →+ ℤ :=
(finsupp.apply_add_hom x).comp (to_finsupp X)

def support (a : free_abelian_group X) : finset X :=
(to_finsupp X a).support

lemma mem_support_iff (x : X) (a : free_abelian_group X) :
  x ∈ a.support ↔ coeff x a ≠ 0 :=
by { rw [support, finsupp.mem_support_iff], exact iff.rfl }

lemma not_mem_support_iff (x : X) (a : free_abelian_group X) :
  x ∉ a.support ↔ coeff x a = 0 :=
by { rw [support, finsupp.not_mem_support_iff], exact iff.rfl }

@[simp] lemma support_zero : support (0 : free_abelian_group X) = ∅ :=
by simp only [support, finsupp.support_zero, add_monoid_hom.map_zero]

@[simp] lemma support_of (x : X) : support (of x) = {x} :=
by simp only [support, to_finsupp_of, finsupp.support_single_ne_zero (one_ne_zero)]

@[simp] lemma support_neg (a : free_abelian_group X) : support (-a) = support a :=
by simp only [support, add_monoid_hom.map_neg, finsupp.support_neg]

@[simp] lemma support_smul (k : ℤ) (h : k ≠ 0) (a : free_abelian_group X) :
  support (k • a) = support a :=
begin
  ext x,
  simp only [mem_support_iff, ← gsmul_eq_smul, add_monoid_hom.map_gsmul],
  simp only [h, gsmul_int_int, false_or, ne.def, mul_eq_zero]
end

open_locale classical

lemma support_add (a b : free_abelian_group X) : (support (a + b)) ⊆ a.support ∪ b.support :=
begin
  simp only [support, add_monoid_hom.map_add],
  apply finsupp.support_add
end

lemma support_sum (s : finset X) (n : X → ℤ) :
  (support (∑ x in s, n x • of x)) ⊆ s :=
begin
  apply finset.induction_on s,
  { simp only [finset.empty_subset, finset.sum_empty, support_zero] },
  intros x s hxs IH,
  rw finset.sum_insert hxs,
  apply finset.subset.trans (support_add _ _),
  by_cases hn : n x = 0,
  { simp only [hn, finset.empty_union, zero_smul, support_zero],
    apply finset.subset.trans IH (finset.subset_insert x s) },
  rw [support_smul _ hn, support_of],
  intros y hy,
  simp only [finset.mem_union, finset.mem_singleton] at hy,
  simp only [finset.mem_insert],
  apply or.imp id _ hy,
  intro h, exact IH h
end

@[simp] lemma coeff_of_self (x : X) : coeff x (of x) = 1 :=
by simp only [coeff, add_monoid_hom.coe_comp, finsupp.apply_add_hom_apply,
      finsupp.single_eq_same, function.comp_app, to_finsupp_of]

lemma sum_support_coeff (a : free_abelian_group X) :
  ∑ x in a.support, coeff x a • (of x) = a :=
begin
  apply (equiv_finsupp X).injective,
  simp only [equiv_finsupp_apply],
  rw [← finsupp.sum_single (to_finsupp X a), finsupp.sum],
  simp only [(to_finsupp X).map_sum, ← gsmul_eq_smul, add_monoid_hom.map_gsmul, to_finsupp_of],
  apply finset.sum_congr rfl,
  intros x hx,
  rw [gsmul_eq_smul],
  convert finsupp.smul_single (coeff x a) x (1:ℤ) using 1,
  { -- this should be easy after bumping mathlib
    sorry },
  { rw [← gsmul_eq_smul, gsmul_one],
    simp only [coeff, int.cast_id, add_monoid_hom.comp_apply, finsupp.apply_add_hom_apply] }
end

-- probably needs a better name
@[elab_as_eliminator] protected lemma induction_on''
  {P : free_abelian_group X → Prop}
  (a : free_abelian_group X)
  (h0 : P 0)
  (h1 : ∀ (n:ℤ) (h : n ≠ 0) x, P (n • of x))
  (h2 : ∀ (a : free_abelian_group X) (n : ℤ) (hn : n ≠ 0) (x : X) (h : x ∉ a.support),
    P a → (∀ (n:ℤ), P (n • of x)) → P (a + n • of x)) :
  P a :=
begin
  rw ← sum_support_coeff a,
  generalize hs : a.support = s,
  classical,
  apply finset.induction_on s; clear_dependent s,
  { simpa only [finset.sum_empty] },
  intros x s hxs IH,
  rw [finset.sum_insert hxs, add_comm],
  by_cases hxa : coeff x a = 0,
  { rw [hxa, zero_smul, add_zero], exact IH },
  apply h2 _ _ hxa _ _ IH,
  { intro n, by_cases hn : n = 0, { rwa [hn, zero_smul] }, exact h1 n hn x },
  contrapose! hxs,
  apply support_sum _ _ hxs
end

end free_abelian_group
