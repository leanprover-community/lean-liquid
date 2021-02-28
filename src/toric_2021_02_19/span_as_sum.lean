import linear_algebra.basis
--import algebra.ring.basic
import ring_theory.subring

section span_as_sum

universe u

open submodule finsupp

open_locale big_operators classical

lemma span_as_sum_converse {R : Type*} {M : Type u} [semiring R] [add_comm_group M] [semimodule R M]
  {m : M} {s : set M}
  (hx : ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ (c.sum (λ i, (smul_add_hom R M).flip i)) = m) :
  m ∈ submodule.span R s :=
begin
  rcases hx with ⟨c, cM, rfl⟩,
  refine sum_mem (span R s) _,
  rintros d ds S ⟨h1, rfl⟩,
  rintros g ⟨h1m : s ⊆ ↑h1, rfl⟩,
  refine h1.smul_mem (c d) _,
  exact @set.mem_of_mem_of_subset M d _ _ ((finset.mem_coe).mpr ds) (set.subset.trans cM h1m),
end

/-- If `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, then we can write
`m` as a finite `R`-linear combination of elements of `s`.
The implementation uses `finsupp.sum`.
The Type `M` has an explicit universe, since otherwise it gets assigned `Type (max u_2 u_3)`.
  -/
--lemma span_as_sum {R : Type*} {M : Type u} [semiring R] [add_comm_group M] [semimodule R M]
--  {m : M} {s : set M} (hm : m ∈ submodule.span R s) :
--  ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ (c.sum (λ i, (smul_add_hom R M).flip i)) = m :=
lemma span_as_sum {R : Type*} {M : Type u} [semiring R] [add_comm_group M] [semimodule R M]
  {m : M} {s : set M} (hm : m ∈ submodule.span R s) :
  ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ (c.sum (λ i, ((smul_add_hom R M).flip) i)) = m :=
begin
  classical,
  refine span_induction hm (λ x hx, _) ⟨0, by simp⟩ _ _; clear hm m,
  { refine ⟨finsupp.single x 1, λ y hy, _, by simp⟩,
    rw [finset.mem_coe, finsupp.mem_support_single] at hy,
    rwa hy.1 },
  { rintros x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩,
    refine ⟨c + d, _, by simp⟩,
    refine set.subset.trans _ (set.union_subset hc hd),
    rw [← finset.coe_union, finset.coe_subset],
    convert finsupp.support_add },
  { rintros r m ⟨c, hc, rfl⟩,
    refine ⟨r • c, λ x hx, hc _, _⟩,
    { rw [finset.mem_coe, finsupp.mem_support_iff] at hx ⊢,
      rw [finsupp.coe_smul] at hx,
      exact right_ne_zero_of_mul hx },
    { rw finsupp.sum_smul_index' (λ (m : M), _),
      { convert (add_monoid_hom.map_finsupp_sum (smul_add_hom R M r) _ _).symm,
        ext m s,
        simp [mul_smul r s m] },
      { exact (((smul_add_hom R M).flip) m).map_zero } } }
end

lemma span_as_sum_iff {R : Type*} {M : Type u} [semiring R] [add_comm_group M] [semimodule R M]
  {m : M} {s : set M} :
  m ∈ submodule.span R s ↔
  ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ (c.sum (λ i, (smul_add_hom R M).flip i)) = m :=
⟨λ h, span_as_sum h, λ h, span_as_sum_converse h⟩

end span_as_sum

section Rnnoneg

variables (R : Type*) [ordered_semiring R]

/--  The subtype of non-negative elements of `R`. -/
def pR : subsemiring R :=
{ carrier := {r : R | 0 ≤ r},
  one_mem' := by simp only [set.mem_set_of_eq, zero_le_one],
  mul_mem' := begin
    rintros x y (x0 : 0 ≤ x) (y0 : 0 ≤ y),
    exact mul_nonneg x0 y0,
  end,
  zero_mem' := rfl.le,
  add_mem' := begin
    rintros x y (x0 : 0 ≤ x) (y0 : 0 ≤ y),
    exact add_nonneg x0 y0,
  end }

/--  The non-negative elements come with a partial order. -/
def popR : partial_order (pR R) := by apply_instance

/--  ... and they form an ordered semiring. -/
instance : ordered_semiring (pR R) :=
{ add_left_cancel := begin
    rintros a ⟨b, b0 : 0 ≤ b⟩ ⟨c, c0 : 0 ≤ c⟩ bc,
    injection bc with hbc,
    simpa only [subtype.mk_eq_mk, add_right_inj] using hbc,
  end,
  add_right_cancel := begin
    rintros ⟨a, a0 : 0 ≤ a⟩ b ⟨c, c0 : 0 ≤ c⟩ ac,
    injection ac with hac,
    simpa only [add_left_inj, subtype.mk_eq_mk] using hac,
  end,
  add_le_add_left := begin
    rintros ⟨a, a0 : 0 ≤ a⟩ ⟨b, b0 : 0 ≤ b⟩ (ab : a ≤ b) ⟨c, c0 : 0 ≤ c⟩,
    apply add_le_add_left ab,
  end,
  le_of_add_le_add_left := begin
    rintros ⟨a, a0 : 0 ≤ a⟩ ⟨b, b0 : 0 ≤ b⟩ ⟨c, c0 : 0 ≤ c⟩ (hbc : a + b ≤ a + c),
    change b ≤ c,
    exact le_of_add_le_add_left hbc,
  end,
  zero_le_one := zero_le_one,
  mul_lt_mul_of_pos_left := λ _ _ _, mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := λ _ _ _, mul_lt_mul_of_pos_right,
  ..(infer_instance : semiring (pR R)),
  ..(infer_instance : partial_order (pR R)) }

end Rnnoneg
