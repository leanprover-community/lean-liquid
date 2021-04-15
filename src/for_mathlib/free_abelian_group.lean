import group_theory.free_abelian_group
import data.finsupp.basic

/-!
In this file we define the equivalence between `free_abelian_group X`
and `X →₀ ℤ` (the type of finitely supported function `X → ℤ`).
Both types come with useful machinery, and the purpose of this file
is to transport some of the machinery from one to the author.

We also define a new induction principle on `free_abelian_group X`,
needed for proving that the maps in `Mbar_complex` compose the way they should.
This induction principle is `induction_on_free_predicate` below.
A `free_predicate` on a free abelian group is a predicate that contains
`a : free_abelian_group X` if and only if it contains all the summands of `a`.
-/

noncomputable theory

open_locale big_operators

namespace int

variables {A : Type*} [add_comm_group A]

-- TODO: should this use `•ℤ` instead? I find the notation a lot uglier
-- But from a Lean point of view it is maybe a lot better.

/-- `int.cast_add_hom' a` is the additive group homomorphism `ℤ → A`
that sends `1 : ℤ` to `a : A`. -/
def cast_add_hom' (a : A) : ℤ →+ A :=
add_monoid_hom.mk' (λ n, n • a) $ λ m n, add_smul _ _ _

@[simp, priority 900]
lemma cast_add_hom'_apply (a : A) (n : ℤ) : cast_add_hom' a n = n • a := rfl

@[simp] lemma cast_add_hom'_one (a : A) : cast_add_hom' a 1 = a :=
by rw [cast_add_hom'_apply, ← gsmul_eq_smul, one_gsmul]

end int

namespace free_abelian_group
variables (X : Type*)

@[simp] lemma map_of' {X Y : Type*} (f : X → Y) (x : X) :
  map f (of x) = of (f x) := rfl

/-- The group homomorphism `free_abelian_group X →+ (X →₀ ℤ)`. -/
def to_finsupp : free_abelian_group X →+ (X →₀ ℤ) :=
free_abelian_group.lift $ λ x, finsupp.single x (1 : ℤ)

/-- The group homomorphism `(X →₀ ℤ) →+ free_abelian_group X`. -/
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

/-- The additive equivalence between `free_abelian_group X` and `(X →₀ ℤ)`. -/
@[simps]
def equiv_finsupp : free_abelian_group X ≃+ (X →₀ ℤ) :=
{ to_fun := to_finsupp X,
  inv_fun := from_finsupp X,
  left_inv := from_finsupp_to_finsupp,
  right_inv := to_finsupp_from_finsupp,
  map_add' := (to_finsupp X).map_add }

variable {X}

/-- `coeff x` is the additive group homomorphism `free_abelian_group X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
def coeff (x : X) : free_abelian_group X →+ ℤ :=
(finsupp.apply_add_hom x).comp (to_finsupp X)

/-- `support a` for `a : free_abelian_group X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
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

@[simp] lemma support_gsmul (k : ℤ) (h : k ≠ 0) (a : free_abelian_group X) :
  support (k •ℤ a) = support a :=
begin
  ext x,
  simp only [mem_support_iff, add_monoid_hom.map_gsmul],
  simp only [h, gsmul_int_int, false_or, ne.def, mul_eq_zero]
end

@[simp] lemma support_smul (k : ℤ) (h : k ≠ 0) (a : free_abelian_group X) :
  support (k • a) = support a :=
by rw [← gsmul_eq_smul, support_gsmul k h]

@[simp] lemma support_smul_nat (k : ℕ) (h : k ≠ 0) (a : free_abelian_group X) :
  support (k • a) = support a :=
by { apply support_smul k _ a, exact_mod_cast h }

open_locale classical

lemma support_add (a b : free_abelian_group X) : (support (a + b)) ⊆ a.support ∪ b.support :=
begin
  simp only [support, add_monoid_hom.map_add],
  apply finsupp.support_add
end

lemma support_add_smul_of (a : free_abelian_group X) (n : ℤ) (hn : n ≠ 0)
  (x : X) (hxa : x ∉ a.support) :
  support (a + n • of x) = insert x a.support :=
begin
  apply finset.subset.antisymm,
  { apply finset.subset.trans (support_add _ _),
    intros y,
    simp only [finset.mem_union, finset.mem_insert, support_smul n hn, support_of, or_comm (y = x),
      finset.mem_singleton, imp_self] },
  { intros y,
    simp only [finset.mem_insert],
    rintro (rfl|hya),
    { rw not_mem_support_iff at hxa,
      simp only [coeff, add_monoid_hom.coe_comp, finsupp.apply_add_hom_apply,
        function.comp_app] at hxa,
      simp only [support, add_monoid_hom.map_add, pi.add_apply, finsupp.mem_support_iff,
        ne.def, finsupp.coe_add, hxa, zero_add, ← gsmul_eq_smul, add_monoid_hom.map_gsmul,
        to_finsupp_of],
      rw [← finsupp.single_add_hom_apply, ← add_monoid_hom.map_gsmul, gsmul_one],
      simpa only [int.cast_id, finsupp.single_eq_same, finsupp.single_add_hom_apply] },
    { rw not_mem_support_iff at hxa,
      rw mem_support_iff at hya,
      simp only [coeff, add_monoid_hom.coe_comp, finsupp.apply_add_hom_apply,
        function.comp_app, ne.def] at hxa hya,
      simp only [support, add_monoid_hom.map_add, pi.add_apply, finsupp.mem_support_iff,
        ne.def, finsupp.coe_add, ← gsmul_eq_smul, add_monoid_hom.map_gsmul, to_finsupp_of],
      rwa [← finsupp.single_add_hom_apply, ← add_monoid_hom.map_gsmul, gsmul_one,
        finsupp.single_add_hom_apply, finsupp.single_apply, if_neg, add_zero],
      rintro rfl, contradiction } }
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
  simp only [← finsupp.single_add_hom_apply, ← add_monoid_hom.map_gsmul, gsmul_one, coeff,
    int.cast_id, add_monoid_hom.comp_apply, finsupp.apply_add_hom_apply]
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

/-- A `free_predicate` on a free abelian group is a predicate that cuts out a subgroup
generated by a subset of the generators of the free abelian group. -/
def free_predicate (Q : free_abelian_group X → Prop) :=
∀ a : free_abelian_group X, Q a ↔ ∀ x ∈ a.support, Q (of x)

namespace free_predicate

variables {Q : free_abelian_group X → Prop} {a b : free_abelian_group X}

lemma zero (h : free_predicate Q) : Q 0 :=
begin
  rw h,
  simp only [finset.not_mem_empty, forall_prop_of_false,
    not_false_iff, support_zero, forall_true_iff]
end

lemma add (h : free_predicate Q) (ha : Q a) (hb : Q b) : Q (a + b) :=
begin
  rw h at ha hb ⊢,
  intros x hx,
  replace hx := support_add _ _ hx,
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

/-- The additive subgroup of elements of `free_abelian_group X` satisfying a given `free_predicate`. -/
def add_subgroup (h : free_predicate Q) : add_subgroup (free_abelian_group X) :=
{ carrier := {a | Q a},
  zero_mem' := h.zero,
  add_mem' := λ a b ha hb, h.add ha hb,
  neg_mem' := λ a ha, h.neg ha }

lemma gsmul (h : free_predicate Q) (n : ℤ) (ha : Q a) : Q (n •ℤ a) :=
add_subgroup.gsmul_mem h.add_subgroup ha n

lemma of_gsmul (h : free_predicate Q) (n : ℤ) (hn : n ≠ 0) (ha : Q (n •ℤ a)) : Q a :=
by { rw h at ha ⊢, simpa only [support_gsmul n hn] using ha }

lemma gsmul_iff (h : free_predicate Q) (n : ℤ) (hn : n ≠ 0) : Q (n •ℤ a) ↔ Q a :=
⟨h.of_gsmul n hn, h.gsmul n⟩

lemma smul (h : free_predicate Q) (n : ℤ) (ha : Q a) : Q (n • a) :=
by { rw ← gsmul_eq_smul, apply h.gsmul _ ha }

lemma of_smul (h : free_predicate Q) (n : ℤ) (hn : n ≠ 0) (ha : Q (n • a)) : Q a :=
by rwa [← gsmul_eq_smul, h.gsmul_iff n hn] at ha

lemma smul_iff (h : free_predicate Q) (n : ℤ) (hn : n ≠ 0) : Q (n • a) ↔ Q a :=
⟨h.of_smul n hn, h.smul n⟩

lemma smul_nat (h : free_predicate Q) (n : ℕ) (ha : Q a) : Q (n • a) :=
h.smul n ha

lemma of_smul_nat (h : free_predicate Q) (n : ℕ) (hn : n ≠ 0) (ha : Q (n • a)) : Q a :=
h.of_smul n (by exact_mod_cast hn) ha

lemma smul_nat_iff (h : free_predicate Q) (n : ℕ) (hn : n ≠ 0) : Q (n • a) ↔ Q a :=
⟨h.of_smul_nat n hn, h.smul_nat n⟩

end free_predicate

/-- An induction principle for elements of `free_abelian_group X`
satisfying some `free_predicate Q`. -/
@[elab_as_eliminator] protected lemma induction_on_free_predicate
  {P : free_abelian_group X → Prop}
  (Q : free_abelian_group X → Prop)
  (hQ : free_predicate Q)
  (a : free_abelian_group X)
  (hQa : Q a)
  (hP0 : P 0)
  (hof : ∀ x, Q (of x) → P (of x))
  (hneg : ∀ a, Q a → P a → P (-a))
  (hadd : ∀ a b, Q a → Q b → P a → P b → P (a + b)) :
  P a :=
begin
  revert hQa,
  have N : ∀ (n:ℕ) x, Q (n • of x) → P (n • of x),
  { intros n x,
    induction n with n ih,
    { intro, exact hP0 },
    { intro hQx,
      have hQ1x : Q (of x) := hQ.of_smul_nat n.succ n.succ_ne_zero hQx,
      have hQnx : Q (n • of x) := hQ.smul_nat n hQ1x,
      rw [nat.succ_eq_add_one, add_smul, one_smul],
      apply hadd _ _ hQnx hQ1x (ih hQnx) (hof _ hQ1x) } },
  apply free_abelian_group.induction_on'' a,
  { intro, exact hP0 },
  { intros n hn x,
    cases le_or_lt 0 n with h0n hn0,
    { lift n to ℕ using h0n, apply N },
    { have h0n : 0 ≤ -n, { rw [neg_nonneg], exact hn0.le },
      lift -n to ℕ using h0n with k hk,
      intro hQx,
      have hQ1x : Q (of x) := hQ.of_smul n hn hQx,
      rw [← neg_neg n, neg_smul],
      apply hneg _ (hQ.smul _ hQ1x),
      rw ← hk,
      exact N _ _ (hQ.smul_nat k hQ1x) } },
  { intros a n hn x hxa IH1 IH2 hq,
    have hQa : Q a,
    { rw hQ at hq ⊢, intros x hxa', apply hq, rw support_add_smul_of _ _ hn _ hxa,
      apply finset.mem_insert_of_mem hxa' },
    have hQx : Q (of x),
    { rw hQ at hq ⊢, intros x' hxa', apply hq, rw support_add_smul_of _ _ hn _ hxa,
      rw [support_of, finset.mem_singleton] at hxa', subst hxa',
      apply finset.mem_insert_self },
    exact hadd _ _ hQa (hQ.smul n hQx) (IH1 hQa) (IH2 n (hQ.smul n hQx)) }
end

lemma mem_support_map {X Y : Type*} (f : X → Y) (hf : function.injective f)
  (a : free_abelian_group X) (y : Y) :
  y ∈ (map f a).support ↔ ∃ x, x ∈ a.support ∧ y = f x :=
begin
  revert y,
  apply free_abelian_group.induction_on'' a; clear a,
  { intro y,
    simp only [finset.not_mem_empty, exists_false, support_zero,
      add_monoid_hom.map_zero, false_and], },
  { intros n hn x y,
    simp only [hn, add_monoid_hom.map_int_module_smul, map_of', support_smul, support_of,
      exists_eq_left, ne.def, not_false_iff, finset.mem_singleton], },
  { rintro a n hn x hx IH - y,
    simp only [add_monoid_hom.map_int_module_smul, add_monoid_hom.map_add, map_of',
      support_add_smul_of _ _ hn _ hx],
    rw support_add_smul_of _ _ hn,
    { simp only [IH, finset.mem_insert],
      split,
      { rintro (rfl|⟨x', h, rfl⟩),
        { exact ⟨x, or.inl rfl, rfl⟩, },
        { exact ⟨x', or.inr h, rfl⟩ } },
      { rintro ⟨x', (rfl|h), rfl⟩,
        { exact or.inl rfl },
        { exact or.inr ⟨x', h, rfl⟩ } } },
    { simp only [IH, not_exists, not_and],
      intros x' hx',
      apply hf.ne,
      rintro rfl,
      exact hx hx' } }
end

end free_abelian_group
#lint- only unused_arguments def_lemma doc_blame
