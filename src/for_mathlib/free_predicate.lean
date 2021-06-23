import data.finsupp.basic
import algebra.big_operators.finsupp
import linear_algebra.finsupp

import for_mathlib.finsupp

noncomputable theory

namespace finsupp

/-- A `free_predicate` on a finitely supported functions is a predicate that cuts out
finitely supported functions whose support is contained in a designated subset. -/
def free_predicate {X A : Type*} [semiring A] (Q : (X →₀ A) → Prop) :=
∀ f, Q f ↔ ∀ x ∈ f.support, Q (single x 1)

namespace free_predicate

variables {X R A : Type*} [semiring R] [ring A] [module R A]
variables {Q : (X →₀ A) → Prop} {a b : X →₀ A}

lemma zero (h : free_predicate Q) : Q 0 :=
begin
  rw h,
  simp only [finset.not_mem_empty, forall_prop_of_false,
    not_false_iff, support_zero, forall_true_iff]
end

lemma add (h : free_predicate Q) (ha : Q a) (hb : Q b) : Q (a + b) :=
begin
  classical,
  rw h at ha hb ⊢,
  intros x hx,
  replace hx := support_add hx,
  simp only [finset.mem_union] at hx,
  cases hx; solve_by_elim
end

lemma neg (h : free_predicate Q) (ha : Q a) : Q (-a) :=
begin
  rw h at ha ⊢,
  intros x hx,
  rw support_neg at hx,
  solve_by_elim
end

lemma neg_iff (h : free_predicate Q) : Q (-a) ↔ Q a :=
⟨λ ha, by simpa only [neg_neg] using h.neg ha, h.neg⟩

/-- The additive subgroup of elements of `X →₀ A` satisfying a given `free_predicate`. -/
def add_subgroup (h : free_predicate Q) : add_subgroup (X →₀ A) :=
{ carrier := {a | Q a},
  zero_mem' := h.zero,
  add_mem' := λ a b ha hb, h.add ha hb,
  neg_mem' := λ a ha, h.neg ha }

lemma smul (h : free_predicate Q) (r : R) (ha : Q a) : Q (r • a) :=
begin
  rw h at ha ⊢,
  intros x hx,
  apply ha,
  rw mem_support_iff at hx ⊢,
  intro hax, apply hx,
  rw [smul_apply, hax, smul_zero],
end

lemma of_smul [no_zero_smul_divisors R A]
  (h : free_predicate Q) (r : R) (hr : r ≠ 0) (ha : Q (r • a)) : Q a :=
begin
  rw h at ha ⊢,
  intros x hx,
  apply ha,
  rw mem_support_iff at hx ⊢,
  intro hax, apply hx,
  rw [smul_apply, smul_eq_zero] at hax,
  exact hax.resolve_left hr
end

lemma smul_iff [no_zero_smul_divisors R A]
  (h : free_predicate Q) (r : R) (hr : r ≠ 0) : Q (r • a) ↔ Q a :=
⟨h.of_smul r hr, h.smul r⟩

end free_predicate

variables {X : Type*}

/-- An induction principle for elements of `X →₀ A`
satisfying some `free_predicate Q`. -/
@[elab_as_eliminator] protected lemma induction_on_free_predicate
  {R : Type*} [semiring R] {P : (X →₀ R) → Prop} (Q : (X →₀ R) → Prop) (hQ : free_predicate Q)
  (a : X →₀ R) (hQa : Q a) (hP0 : P 0) (hof : ∀ x r, Q (single x r) → P (single x r))
  (hadd : ∀ a b, Q a → Q b → P a → P b → P (a + b)) :
  P a :=
begin
  revert hQa,
  apply finsupp.induction_on'' a,
  { intro, exact hP0 },
  { intros n hn x, apply hof },
  { intros a n hn x hxa IH1 IH2 hq,
    suffices H : Q a ∧ Q (single x n),
    { exact hadd _ _ H.1 H.2 (IH1 H.1) (IH2 _ H.2) },
    classical,
    have aux : disjoint a.support (single x n).support,
    { rwa [support_single_ne_zero hn, finset.disjoint_singleton], },
    split; id { rw hQ at hq ⊢, intros x' hxa', apply hq, rw support_add_eq aux, },
    { apply finset.subset_union_left, exact hxa' },
    { apply finset.subset_union_right, exact hxa' }, },
end

/-- An induction principle for elements of `X →₀ A`
satisfying some `free_predicate Q`. -/
@[elab_as_eliminator] protected lemma induction_on_free_predicate_nat
  {P : (X →₀ ℕ) → Prop} (Q : (X →₀ ℕ) → Prop) (hQ : free_predicate Q)
  (a : X →₀ ℕ) (hQa : Q a) (hP0 : P 0) (hof : ∀ x, Q (single x 1) → P (single x 1))
  (hadd : ∀ a b, Q a → Q b → P a → P b → P (a + b)) :
  P a :=
begin
  refine finsupp.induction_on_free_predicate Q hQ a hQa hP0 _ hadd,
  intros x n hQn,
  induction n with n ih, { rwa [single_zero] },
  rw [nat.succ_eq_add_one, single_add],
  suffices : ∀ k, Q (single x k), { apply_rules [hadd, hof, ih, this], },
  intro k,
  rw hQ at hQn ⊢, intros y hy, apply hQn,
  rw support_single_ne_zero n.succ_ne_zero,
  apply support_single_subset hy,
end

/-- An induction principle for elements of `X →₀ A`
satisfying some `free_predicate Q`. -/
@[elab_as_eliminator] protected lemma induction_on_free_predicate_int
  {P : (X →₀ ℤ) → Prop} (Q : (X →₀ ℤ) → Prop) (hQ : free_predicate Q)
  (a : X →₀ ℤ) (hQa : Q a) (hP0 : P 0) (hof : ∀ x, Q (single x 1) → P (single x 1))
  (hneg : ∀ a, Q a → P a → P (-a)) (hadd : ∀ a b, Q a → Q b → P a → P b → P (a + b)) :
  P a :=
begin
  refine finsupp.induction_on_free_predicate Q hQ a hQa hP0 _ hadd,
  have aux : ∀ x (n:ℕ), Q (single x n) → P (single x n),
  { intros x n,
    induction n with n ih,
    { intro, erw single_zero, exact hP0 },
    { intro hQx,
      have hQ1x : Q (single x 1),
      { rw ← smul_single_one at hQx,
        refine hQ.of_smul _ _ hQx,
        exact_mod_cast n.succ_ne_zero },
      have hQnx : Q (single x n),
      { rw ← smul_single_one, exact hQ.smul n hQ1x },
      push_cast,
      rw [single_add],
      apply hadd _ _ hQnx hQ1x (ih hQnx) (hof _ hQ1x) } },
  intros x n,
  cases le_or_lt 0 n with h0n hn0,
  { lift n to ℕ using h0n, apply aux, },
  { have h0n : 0 ≤ -n, { rw [neg_nonneg], exact hn0.le },
    lift -n to ℕ using h0n with k hk,
    intro hQx,
    rw [← neg_neg n, single_neg, ← hk],
    suffices : Q (single x ↑k), { apply_rules [hneg, aux], },
    rwa [hk, single_neg, hQ.neg_iff] },
end

end finsupp
