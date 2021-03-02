import linear_algebra.basis
--import algebra.ring.basic
import ring_theory.subring
--open submodule finsupp

variables {R : Type*} [comm_semiring R]




variables {p : R → Prop} (p0 : p 0) (p1 : p 1)
  (padd : ∀ {a b : R}, p a → p b → p (a + b))
  (pmul : ∀ {a b : R}, p a → p b → p (a * b))

namespace subtype_comm_semiring

section pR

variable (p)

def pR : Type* := {r : R // p r}

end pR

instance comm_semiring : comm_semiring (pR p) := sorry

instance has_add : has_add (pR p) :=
{ add := λ x y, ⟨x.1 + y.1, padd x.2 y.2⟩ }

instance comm_semiring : comm_semiring (pR p) :=
{ add := by library_search,
  add_assoc := λ x y z, by simp only [subtype.val_eq_coe, add_assoc],
  zero := ⟨_, p0⟩,
  zero_add := by library_search,
  add_zero := _,
  add_comm := _,
  mul := λ x y, ⟨x.1 * y.1, pmul x.2 y.2⟩,
  mul_assoc := λ x y z, by simp only [subtype.val_eq_coe, mul_assoc] },
  one := ⟨_, p1⟩,
  one_mul := λ ⟨x, _⟩, by simpa [(*)] using one_mul x,
  mul_one := λ ⟨x, _⟩, by simpa [(*)] using mul_one x,
  zero_mul := _,
  mul_zero := _,
  left_distrib := _,
  right_distrib := _,
  mul_comm := _ }

end subtype_comm_semiring

def Rnonneg [has_zero R] [has_le R] : Type* := {r : R // 0 ≤ r}

namespace Rnonneg



lemma add_closure [semigroup R] {p : R → Prop} (pmul : ∀ {a b : R}, p a → p b → p (a * b)) :
  semigroup {r : R // p r} :=
{ mul := λ x y, ⟨x.1 * y.1, pmul x.2 y.2⟩,
  mul_assoc := λ x y z, by simp only [subtype.val_eq_coe, mul_assoc] }

lemma comm_group [comm_group R] {p : R → Prop}
  (p1 : p 1)
  (pmul : ∀ {a b : R}, p a → p b → p (a * b))
  (pinv : ∀ {a : R}, p a → p a⁻¹) :
  comm_group {r : R // p r} :=
{ mul := λ x y, ⟨x.1 * y.1, pmul x.2 y.2⟩,
  mul_assoc := λ x y z, by simp only [subtype.val_eq_coe, mul_assoc],
  one := ⟨1, p1⟩,
  one_mul := λ ⟨x, _⟩, by simpa [(*)] using one_mul x,
  mul_one := λ ⟨x, _⟩, by simpa [(*)] using mul_one x,
  inv := λ x, ⟨_, pinv x.2⟩,
  div := λ x y, x * ⟨_, pinv y.2⟩,
  div_eq_mul_inv := _,
  mul_left_inv := _,
  mul_comm := _ }

instance inhabited [ordered_semiring R] : inhabited (Rnonneg R) :=
{ default := { val := 0,
  property := rfl.le } }

instance has_coe : has_coe (Rnonneg R) R :=
{ coe := λ x, x.1 }

instance has_add : has_add (Rnonneg R) :=
{ add := λ x y, ⟨x.1 + y.1, add_nonneg x.2 y.2⟩ }

instance Rnnonneg_semiring : semiring (Rnonneg R) :=
{ add := (+),
  add_assoc := _,
  zero := _,
  zero_add := _,
  add_zero := _,
  add_comm := _,
  mul := _,
  mul_assoc := _,
  one := _,
  one_mul := _,
  mul_one := _,
  zero_mul := _,
  mul_zero := _,
  left_distrib := _,
  right_distrib := _ }

end Rnonneg

#exit
universe u

lemma set_finset {R : Type*} {M : Type u}
  [semiring R]
  [add_comm_group M]
  [semimodule R M]
  (T : finset M) (m : M) (s : set M) (Ts : ↑T ⊆ s)
  (t : M)
  (ht : t ∈ T)
--  (this : T = insert t (finset.erase T t))
  (mT : m ∈ span R ((insert t (finset.erase T t) : finset M) : set M))
  --(this : insert t (T : set M) = (T : set M))
   :
  m ∈ span R (insert t (finset.erase T t) : set M) :=
begin
  convert mT,
  simp,
end

example {R : Type*} {M : Type u} (_inst : Π (a : Prop), decidable a) (n : ℕ)
  (T : finset M) (m : M) (s : set M) (Ts : ↑T ⊆ s)
  (Tc : finset.card T = n.succ)
  [semiring R]
  [add_comm_group M]
  [semimodule R M]
  (t : M)
  (ht : t ∈ T)
  (this : T = insert t (finset.erase T t))
  (mT : m ∈ span R ((insert t (finset.erase T t)) : set M))
  (this : insert t (T : set M) = ↑T) :
  insert t (((finset.erase T t) : finset M) : set M) = (insert t (finset.erase T t)) :=
begin
  simp,
end

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


noncomputable def lc_of_span {R : Type*} {M : Type u} [semiring R] [add_comm_group M] [semimodule R M]
  (s : set M) : M →₀ R :=
begin
  classical,
  refine ⟨_, _, _⟩,
  rotate,
  intros m,
  by_cases hm : m ∈ submodule.span R s,
  {
  -- the element `m` is in the span of `s`, if it is in the span of a finite subset `T ⊆ s`
  obtain F := mem_span_finite_of_mem_span hm,
  choose T Tv mT using F,
  -- now that we know that our element `m` is in the span of `T ⊆ S`, we no longer need to carry
  -- around that it is also in the span of `S`
  clear hm,
  -- induction on the finset `T`: the base case `T = ∅` is trivial.
  generalize' hT : T.card = n,
  -- prepare for doing induction on
  revert T m s,
  induction n with n ih,
  { exact λ T m s Ts mT Tc, 0 },
  {
    refine λ T m s Ts mT Tc, _,
--    have T0 : T.card ≠ 0, { rw Tc, exact nat.succ_ne_zero _ },
    have : ∃ t : M, t ∈ T,
    { rcases finset.eq_empty_or_nonempty T with (rfl | hT),
      { exact nat.no_confusion Tc },
      { exact finset.nonempty.bex hT } },
    choose t ht using this,
    have : T = insert t (T.erase t) := (finset.insert_erase ht).symm,
    rw this at mT,
    have tTT : insert t (T : set M) = T, { rw set.insert_eq_of_mem,exact finset.mem_coe.mpr ht },
    have : m ∈ span R (insert t ↑(finset.erase T t)),
    { convert mT,
      --simp only [finset.coe_insert, set.insert_diff_singleton, finset.coe_erase],
      simp only [finset.coe_insert] },
    obtain F := (@mem_span_insert R M _ _ _ m (T.erase t) t).mp this,
    choose a z hz ide using F,
    exact a } },
  { exact 0 },
  intros a,
  refine ⟨_, _⟩,
  sorry,sorry,sorry,
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



/-  Ideally, I would be able to prove this using the lemma above, but I cannot... -/
lemma submodule.span_as_sum_mine {R M : Type*} [semiring R] [add_comm_group M] [semimodule R M]
  {m : M} {s : set M} (hm : m ∈ submodule.span R s) :
  ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ (∑ i in c.support, c i • i) = m :=
begin
  exact span_as_sum hm,
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
    ih rfl.subset hz,
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

#check @submodule.span_as_sum
#check @submodule.span_as_sum_mine

#exit

lemma submodule.span_as_sum_kevin {R M : Type*} [semiring R] [add_comm_group M] [semimodule R M]
  {m : M} {s : set M} (hm : m ∈ submodule.span R s) :
  ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ (∑ i in c.support, c i • i) = m :=
begin
  by_cases tr : (1 : R) = 0,
  refine ⟨0, _, _⟩,
  { simp only [set.empty_subset, finset.coe_empty, finsupp.support_zero] },
  { rw [← one_smul R m, tr],
    simp only [finsupp.coe_zero, zero_smul, finset.sum_const_zero] },
--  haveI : nontrivial R:= nontrivial_of_ne 1 0 tr,
  apply span_induction hm,
  { refine λ x xs, ⟨finsupp.single x 1, _, _⟩,
    { rw finsupp.support_single_ne_zero tr,
      exact finset.singleton_subset_set_iff.mpr xs },
    { rw finsupp.support_single_ne_zero tr,
      simp } },
  { refine ⟨0, _, _⟩,
    { simp only [set.empty_subset, finset.coe_empty, finsupp.support_zero] },
    { simp only [finsupp.coe_zero, zero_smul, finset.sum_const_zero]} },
  {
    rintros x y ⟨cx, cxs, rfl⟩ ⟨cy, cys, rfl⟩,
    refine ⟨cx + cy, _, _⟩,
    sorry,--inclusions
    simp,
    sorry,
  },
  {
    rintros a x ⟨cx, cxs, rfl⟩,
    refine ⟨a • cx, _, _⟩,
  },
end



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
