import data.finsupp.basic
import algebra.big_operators.finsupp
import linear_algebra.finsupp

noncomputable theory

namespace finsupp

@[simp] lemma lift_single {R M X : Type*} [semiring R] [add_comm_monoid M] [module R M]
  (f : X → M) (x : X) (r : R) :
  finsupp.lift M R X f (single x r) = r • (f x) :=
begin
  simp only [lift, linear_map.map_zero, add_equiv.arrow_congr_apply, linear_equiv.coe_to_add_equiv,
    id.def, sum_single_index, add_equiv.coe_trans, coe_lsum, equiv.refl_symm, equiv.coe_refl],
  refl
end

variables {X : Type*}

instance : no_zero_smul_divisors ℕ ℤ :=
{ eq_zero_or_eq_zero_of_smul_eq_zero := λ k n,
  by simp only [imp_self, int.coe_nat_eq_zero, nsmul_eq_mul, int.nat_cast_eq_coe_nat, mul_eq_zero] }

-- probably needs a better name
@[elab_as_eliminator] protected lemma induction_on'' {R : Type*} [semiring R]
  {P : (X →₀ R) → Prop}
  (a : (X →₀ R))
  (h0 : P 0)
  (h1 : ∀ (n:R) (h : n ≠ 0) x, P (single x n))
  (h2 : ∀ (a : X →₀ R) (n : R) (hn : n ≠ 0) (x : X) (h : x ∉ a.support),
    P a → (∀ (n:R), P (single x n)) → P (a + single x n)) :
  P a :=
begin
  rw [← a.sum_single, finsupp.sum],
  generalize hs : a.support = s,
  classical,
  apply finset.induction_on s; clear_dependent s,
  { simpa only [finset.sum_empty] },
  intros x s hxs IH,
  rw [finset.sum_insert hxs, add_comm],
  by_cases hxa : a x = 0,
  { simp only [hxa, add_zero, single_zero], exact IH },
  apply h2 _ _ hxa _ _ IH,
  { intro n, by_cases hn : n = 0, { rwa [hn, single_zero] }, exact h1 n hn x },
  simp only [not_mem_support_iff, finset.sum_apply', single_apply, finset.sum_ite_eq'],
  rwa if_neg,
end

-- generalize?
lemma mem_support_map_domain {X Y : Type*} (f : X → Y) (hf : function.injective f)
  (a : X →₀ ℤ) (y : Y) :
  y ∈ (map_domain f a).support ↔ ∃ x, x ∈ a.support ∧ y = f x :=
begin
  revert y,
  apply finsupp.induction_on'' a; clear a,
  { intro y,
    simp only [finset.not_mem_empty, exists_false, map_domain_zero, support_zero, false_and], },
  { intros n hn x y,
    simp only [hn, map_domain_single, support_single_ne_zero hn,
      exists_eq_left, ne.def, not_false_iff, finset.mem_singleton], },
  { rintro a n hn x hx IH - y,
    simp only [map_domain_add, map_domain_single],
    classical,
    have aux1 : disjoint a.support (single x n).support,
    { rwa [support_single_ne_zero hn, finset.disjoint_singleton] },
    have aux2 : disjoint (map_domain f a).support (single (f x) n).support,
    { rw [support_single_ne_zero hn, finset.disjoint_singleton, IH],
      simpa only [hf.eq_iff, not_not, exists_eq_right'], },
    simp only [support_add_eq, aux1, aux2],
    { simp only [support_single_ne_zero hn, IH, finset.mem_union, finset.mem_singleton],
      split,
      { rintro (⟨x', h, rfl⟩|rfl),
        { exact ⟨x', or.inl h, rfl⟩ },
        { exact ⟨x, or.inr rfl, rfl⟩ } },
      { rintro ⟨x', (h|rfl), rfl⟩,
        { exact or.inl ⟨x', h, rfl⟩ },
        { exact or.inr rfl } } } }
end

end finsupp
