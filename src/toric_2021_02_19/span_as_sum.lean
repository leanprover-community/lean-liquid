import linear_algebra.basis

open submodule

open_locale big_operators classical

lemma submodule.span_as_sum {R M : Type*} [semiring R] [add_comm_group M] [semimodule R M]
  {m : M} {s : set M} (hm : m ∈ submodule.span R s) :
  ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ (∑ i in c.support, c i • i) = m :=
begin
  -- the element `m` is in the span of `s`, if it is in the span of a finite subset `T ⊆ s`
  obtain ⟨T, Tv, mT⟩ := mem_span_finite_of_mem_span hm,
  -- now that we know that our element `m` is in the span of `T ⊆ S`, we no longer need to carry
  -- around that it is also in the span of `S`
  clear hm,
  -- prepare for doing induction on
  revert m s,
  -- induction on the finset `T`: the base case `T = ∅` is trivial.
  refine finset.induction_on T (λ m s es me, ⟨0, by simpa [eq_comm] using me⟩) _,
  -- clear unneded clutter (not sure why this did not go away on its own)
  clear T,
  -- induction step: we add an element `m1` to the finset `T`, we have an element `m`
  -- in the span of `T ∪ {m1}`
  refine λ m1 T m1T ih m s ims m1i, _,
  -- move sets/finsets around
  rw [finset.coe_insert] at m1i,
  -- we isolate the coefficient `a` of `m1`
  obtain ⟨a, z, hz, rfl⟩ : ∃ (a : R) (z : M) (H : z ∈ span R ↑T), m = a • m1 + z :=
    mem_span_insert.mp m1i,
  -- apply the induction hypothesis to obtain the coefficients for the elements of `T`
  obtain ⟨c1, c1ss, rfl⟩ : ∃ (c : M →₀ R), (c.support) ⊆ T ∧ ∑ (i : M) in c.support, c i • i = z :=
    ih z T rfl.subset hz,
  -- separate the cases in which the coefficient `a` of the "new" element `m1` vanishes...
  by_cases a0 : a = 0,
  { -- in this case, the coefficients that we get by induction work straight away
    refine ⟨c1, λ g hg, ims (finset.mem_insert_of_mem (c1ss hg)), _⟩,
    rw [a0, zero_smul, zero_add] },
  -- or the new coefficient `a` is non-zero
  -- the new element `m1` is not in the support of the coefficients for `m` arising from the
  -- induction hypothesis
  have mc1 : m1 ∉ c1.support := λ h, m1T (finset.mem_coe.mp (set.mem_of_mem_of_subset h c1ss)),
  -- by construction, the support of `c1` does not contain `m1`
  have dc1m : disjoint c1.support (finsupp.single m1 a).support,
  { rw [finsupp.support_single_ne_zero a0],
    exact finset.disjoint_singleton.mpr mc1 },
  -- moreover, the involved coefficients are really the coefficients appearing in the support
  -- of `c1` and `{m1}`
  have cpa : (c1 + finsupp.single m1 a).support = c1.support ∪ {m1},
  { ext x,
    rw ← finsupp.support_single_ne_zero a0,
    refine ⟨λ h, finsupp.support_add h, λ h, _⟩,
    refine finset.mem_of_subset (eq.subset _) h,
    rw finsupp.support_add_eq dc1m },
  -- of course, `m` is the sum of the coefficients coming from the induction and
  -- the new coefficient `a` for `m1`
  refine ⟨c1 + finsupp.single m1 a, λ h hs, ims _, _⟩,
  -- make sure that the support is still contained in `T ∪ {m1}`
  { -- we use `hs`, once we undo trivialities
    rw [cpa, finset.union_comm] at hs,
    refine set.mem_of_mem_of_subset hs _,
    rw [← finset.insert_eq, finset.coe_insert, finset.coe_insert],
    exact set.insert_subset_insert c1ss },
  -- in this branch, we show that the element `m` really is the sum that we claim it is
  { -- remove clutter from the proof
    clear m1i m1T hz ih,
    -- a complicated way of writing `a • m1`, as a sum over the singleton `{m1}`
    have : ∑ (x : M) in {m1}, (c1 + finsupp.single m1 a) x • x = a • m1,
    { rw [finset.sum_singleton, finsupp.coe_add, pi.add_apply, add_smul, finsupp.single_eq_same],
      refine add_left_eq_self.mpr _,
      rw [finsupp.not_mem_support_iff.mp mc1, zero_smul] },
    -- we start by matching up term, first one of the sums equals `a • m1`
    rw [cpa, finset.sum_union (by rwa finsupp.support_single_ne_zero a0 at dc1m), add_comm,
      this, finsupp.coe_add],
    -- next, we split the other sum
    simp_rw [pi.add_apply, add_smul, finset.sum_add_distrib],
    -- now we clear `a • m1` and one of the sums, since they are equal on both sides
    refine (add_right_inj _).mpr (add_right_eq_self.mpr _),
    -- we show that the remaining sum vanishes, by showing that all its terms vanish
    refine finset.sum_eq_zero (λ x xc1, _),
    -- it suffices to show that we are `smul`ling by `0`
    convert zero_smul _ x,
    -- for this, it suffices to show that `x` is not equal to `m1`
    rw [← finsupp.not_mem_support_iff, finsupp.support_single_ne_zero a0, finset.not_mem_singleton],
    -- since `x` is in the support of `c1`, it follows that `x ≠ m1`, the proof is by contradiction
    rintros rfl,
    exact mc1 xc1 }
end


#exit

lemma submodule.span_as_sum {R : Type*} [semiring R] [semimodule R M]
  (m : M) (s : set M) (hm : m ∈ submodule.span R s) :
  ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ (∑ i in c.support, c i • i) = m :=
begin
  -- the element `m` is in the span of `s`, if it is in the span of a finite subset `T ⊆ s`
  obtain ⟨T, Tv, mT⟩ := mem_span_finite_of_mem_span hm,
  -- now that we know that our element `m` is in the span of `T ⊆ S`, we no longer need to carry
  -- around that it is also in the span of `S`
  clear hm,
  -- prepare for doing induction on
  revert m s,
  -- induction on the finset `T`: the base case `T = ∅` is trivial.
  refine finset.induction_on T (λ m s es me, ⟨0, by simpa [eq_comm] using me⟩) _,
  -- clear unneded clutter (not sure why this did not go away on its own)
  clear T,
  -- induction step: we add an element `m1` to the finset `T`, we have an element `m`
  -- in the span of `T ∪ {m1}`
  refine λ m1 T m1T ih m s ims m1i, _,
  -- move sets/finsets around
  rw [finset.coe_insert] at m1i,
  -- we isolate the coefficient `a` of `m1`
  obtain ⟨a, z, hz, rfl⟩ : ∃ (a : R) (z : M) (H : z ∈ span R ↑T), m = a • m1 + z :=
    mem_span_insert.mp m1i,
  -- apply the induction hypothesis to obtain the coefficients for the elements of `T`
  obtain ⟨c1, c1ss, rfl⟩ : ∃ (c : M →₀ R), (c.support) ⊆ T ∧ ∑ (i : M) in c.support, c i • i = z :=
    ih z T rfl.subset hz,
  -- separate the cases in which the coefficient `a` of the "new" element `m1` vanishes...
  by_cases a0 : a = 0,
  { -- in this case, the coefficients that we get by induction work straight away
    refine ⟨c1, λ g hg, ims (finset.mem_insert_of_mem (c1ss hg)), _⟩,
    rw [a0, zero_smul, zero_add] },
  -- or the new coefficient `a` is non-zero
  -- the new element `m1` is not in the support of the coefficients for `m` arising from the
  -- induction hypothesis
  have mc1 : m1 ∉ c1.support := λ h, m1T (finset.mem_coe.mp (set.mem_of_mem_of_subset h c1ss)),
    have dc1m : disjoint c1.support (finsupp.single m1 a).support,
    { rw [finsupp.support_single_ne_zero a0],
      exact finset.disjoint_singleton.mpr mc1 },
    have cpa : (c1 + finsupp.single m1 a).support = c1.support ∪ {m1},
    { ext x,
      rw ← finsupp.support_single_ne_zero a0,
      refine ⟨λ h, finsupp.support_add h, λ h, _⟩,
      refine finset.mem_of_subset (eq.subset _) h,
      rw finsupp.support_add_eq dc1m },
  -- of course, the expression of `m` is as the sum of the coefficients coming from the induction
  -- and the new coefficient `a` for `m1`
  refine ⟨c1 + finsupp.single m1 a, λ h hs, ims _, _⟩,
  { rw [finset.mem_coe, finset.insert_eq, finset.mem_union, finset.mem_singleton],
    obtain F : h = m1 ∨ h ∈ c1.support.val := by simpa [finsupp.support_single_ne_zero a0,
      finset.union_comm] using set.mem_of_mem_of_subset hs finsupp.support_add,
    cases F,
    { exact or.inl F },
    { exact or.inr (finset.coe_subset.mp c1ss F) } },
  { clear m1i m1T hz ih,
    have : ∑ (x : M) in {m1}, (c1 + finsupp.single m1 a) x • x = a • m1,
    { rw [finset.sum_singleton, finsupp.coe_add, pi.add_apply, add_smul, finsupp.single_eq_same],
      refine add_left_eq_self.mpr _,
      rw [finsupp.not_mem_support_iff.mp mc1, zero_smul] },
    rw [cpa, finset.sum_union (by rwa finsupp.support_single_ne_zero a0 at dc1m), add_comm],
    rw [this, finsupp.coe_add],
    simp_rw [pi.add_apply, add_smul, finset.sum_add_distrib],
    refine (add_right_inj _).mpr (add_right_eq_self.mpr _),
    refine finset.sum_eq_zero (λ x xc1, _),
    convert zero_smul _ x,
    rw [← finsupp.not_mem_support_iff, finsupp.support_single_ne_zero a0, finset.not_mem_singleton],
    rintros rfl,
    exact mc1 xc1 }
end




lemma submodule.span_as_sum {R : Type*} [semiring R] [semimodule R M]
  (m : M) (s : set M) (hm : m ∈ submodule.span R s) :
  ∃ su : finset M, ∃ c : M →₀ R,
    c.support = su ∧ (c.support : set M) ⊆ s ∧ ((∑ i in su, c i • i) = m) :=
--  ∃ c : finsupp M R, ((c.support : set M) ⊆ s) ∧ ((∑ i ∈ c.support, c i • i) = m) :=
begin
  obtain ⟨T, Tv, mT⟩ := mem_span_finite_of_mem_span hm,
  revert mT Tv m s,
  refine finset.induction_on T _ _,
  { refine λ m s ms es me, _,
    exact ⟨∅, 0, finsupp.support_zero, by simpa [eq_comm] using me⟩ },
  refine λ m S ms ih m1 s m1s ims m1i, _,
  rw [finset.coe_insert] at m1i,
  choose a z hz ide using mem_span_insert.mp m1i,
  subst ide,
  by_cases a0 : a = 0,
  { subst a0,
    rw [zero_smul, zero_add] at m1s m1i,
    obtain ⟨su, c, csu, cS, F⟩ := ih _ _ hz rfl.subset hz,
    simp_rw [zero_smul, zero_add],
    refine ⟨su, c, csu, _, F⟩,
    refine λ g hg, ims _,
    rw [finset.coe_insert, set.mem_insert_iff],
    exact or.inr (cS hg) },
  obtain F := ih z S hz rfl.subset hz,
  choose su c1 c1s c1ss ide using F,
  have mc1 : m ∉ c1.support := λ h, ms (finset.mem_coe.mp (set.mem_of_mem_of_subset h c1ss)),
  subst ide,
  subst c1s,
  refine ⟨insert m c1.support, c1 + finsupp.single m a, _, _, _⟩,
  { rw [add_comm, finsupp.support_add_eq, finsupp.support_single_ne_zero a0, finset.insert_eq],
    rwa [finsupp.support_single_ne_zero a0, finset.singleton_disjoint] },
  { intros h hs,
    apply ims,
    have : (c1 + finsupp.single m a).support ⊆ c1.support ∪ (finsupp.single m a).support :=
      finsupp.support_add,
    rw finset.insert_eq,
    rw [finsupp.support_single_ne_zero a0, finset.union_comm] at this,
    obtain F := set.mem_of_mem_of_subset hs this ,
    simp at F ⊢,
    cases F,
    exact or.inl F,
    refine or.inr _,
    simp at c1ss,
    exact c1ss F },
  { rw finset.sum_insert mc1,
    simp only [pi.add_apply, finsupp.coe_add],
    simp_rw [add_smul, finset.sum_add_distrib],
    rw add_comm,
    rw [finsupp.single_eq_same],
    rw [add_comm (a • m), ← add_assoc],
    simp only [add_left_inj],
    rw [add_assoc, ← add_zero (∑ (i : M) in c1.support, c1 i • i)],
    simp only [add_right_eq_self],
    have c10: c1 m = 0 := finsupp.not_mem_support_iff.mp mc1,
    rw [c10, zero_smul, add_zero],
    apply finset.sum_eq_zero,
    intros x xc1,
    convert zero_smul _ x,
    rw [← finsupp.not_mem_support_iff, finsupp.support_single_ne_zero a0],
    simp only [ne.def, finset.mem_singleton],
    rintros rfl,
    exact mc1 xc1 }
end

#exit
