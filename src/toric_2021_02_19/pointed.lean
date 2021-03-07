import algebra.regular
import linear_algebra.finite_dimensional
import linear_algebra.basis
import toric_2021_02_19.is_inj_nonneg

/-! In the intended application, these are the players:
* `R = ℕ`;
* `S = ℤ`;
* `M` is a free finitely generated `ℤ`-module.
-/

open_locale big_operators

variables {R S M : Type*}

namespace submodule

section semiring_S_add_comm_monoid_M

/-  The `is_scalar_tower R S M` assumption is not needed to state `pointed`, but will likely play
a role in the proof of `sup_extremal_rays`. -/
variables (S) [semiring S] [add_comm_monoid M] [semimodule S M]

section semiring_R

variables [semiring R] [semimodule R M]
/--  A pointed submodule is a submodule `s` for which there exists a linear function `φ : M → S`,
such that the hyperplane `ker φ` intersects `s` in just the origin.
Alternatively, the submodule `s` contains no `S` linear subspace. -/
def pointed (s : submodule R M) : Prop := ∃ φ : M →ₗ[S] S, ∀ x : M, x ∈ s → φ x = 0 → x = 0

/--  A pointed subset is a submodule `s` for which there exists a linear function `φ : M → S`,
such that the hyperplane `ker φ` intersects `s` in just the origin. -/
-- We may not need this definition.
def pointed_subset (s : set M) : Prop := ∃ φ : M →ₗ[S] S, ∀ x : M, x ∈ s → φ x = 0 → x = 0

end semiring_R

section comm_semiring_R

variables [comm_semiring R] [semimodule R M] [algebra R S] [is_scalar_tower R S M]

/--  A submodule of a pointed submodule is pointed. -/
lemma pointed_of_submodule {s t : submodule R M} (st : s ≤ t) (pt : pointed S t) : pointed S s :=
begin
  cases pt with l hl,
  exact ⟨l, λ m ms m0, hl m (st ms) m0⟩,
end

/-- Any `R`-submodule of `S` is pointed, since the identity function is a "separating hyperplane".
This should not happen if the module is not cyclic for `S`. -/
lemma pointed_of_sub_R {s : submodule R S} : pointed S s :=
⟨1, λ _ _ h, h⟩

/-- The zero submodule of any `R`-module `M` is pointed, since the zero function is a
"separating hyperplane". -/
lemma pointed_of_bot : pointed S (⊥ : submodule R M) :=
⟨0, λ x xb h, xb⟩

lemma fd {ι : Type*} (v : ι → S) (ind : linear_independent S v) :
  pointed S (submodule.span R (v '' set.univ)) :=
pointed_of_sub_R S

end comm_semiring_R

end semiring_S_add_comm_monoid_M

end submodule

namespace pairing

open pairing submodule

variables [ordered_comm_ring S]

variables [add_comm_group M] [comm_semiring R] [semimodule R M] [module S M]
variables [algebra R S] [is_scalar_tower R S M]

lemma no_zero_divisors.pointed_of_span_pos_is_inj [no_zero_divisors S] {s : set M} {l : M →ₗ[S] S}
  (lpos : ∀ {a : M}, a ∈ s → 0 < l a) (hRS : is_inj_nonneg (algebra_map R S)) :
  pointed S (submodule.span R s) :=
begin
  refine ⟨l, λ m hm m0, _⟩,
  obtain ⟨c, csup, rfl⟩ := mem_span_set.mp hm,
  rw ← @finset.sum_const_zero _ _ c.support,
  refine finset.sum_congr rfl (λ x hx, _),
  change l (∑ i in c.support, c i • i) = 0 at m0,
  simp_rw [linear_map.map_sum, linear_map.map_smul_of_tower] at m0,
  obtain F := (finset.sum_eq_zero_iff_of_nonneg (λ m hx, _)).mp m0 _ hx,
  { rw [← algebra_map_smul S (c x) (l x), smul_eq_mul, mul_eq_zero] at F,
    rcases F with c0 | l0,
    { convert zero_smul R x,
      refine hRS.1 _,
      simpa using c0 },
    { exact ((lpos (set.mem_of_mem_of_subset (finset.mem_coe.mpr hx) csup)).ne' l0).elim } },
  { rw [← algebra_map_smul S (c m) (l m), smul_eq_mul],
    exact mul_nonneg (hRS.2 _) (lpos (set.mem_of_mem_of_subset (finset.mem_coe.mpr hx) csup)).le }
end

lemma span_pointed_of_pos_reg_is_inj {s : set M} (l : M →ₗ[S] S)
  (lpos : ∀ {a : M}, a ∈ s → 0 ≤ l a ∧ is_regular (l a)) (hRS : is_inj_nonneg (algebra_map R S)) :
  pointed S (submodule.span R s) :=
begin
  refine ⟨l, λ m hm m0, _⟩,
  obtain ⟨c, csup, rfl⟩ := mem_span_set.mp hm,
  rw ← @finset.sum_const_zero _ _ c.support,
  refine finset.sum_congr rfl (λ x hx, _),
  change l (∑ i in c.support, c i • i) = 0 at m0,
  simp_rw [linear_map.map_sum, linear_map.map_smul_of_tower] at m0,
  obtain F := (finset.sum_eq_zero_iff_of_nonneg (λ m hx, _)).mp m0 _ hx,
  { dsimp,
    have : (algebra_map R S) (c x) = 0,
    { refine (lpos (set.mem_of_mem_of_subset (finset.mem_coe.mpr hx) csup)).2.right _,
      rw [← algebra_map_smul S (c x) (l x), smul_eq_mul] at F,
      simpa only [zero_mul] },
    rw [← algebra_map_smul S (c x) x, this, zero_smul] },
  { rw [← algebra_map_smul S (c m) (l m), smul_eq_mul],
    exact mul_nonneg (hRS.2 _) (lpos (set.mem_of_mem_of_subset (finset.mem_coe.mpr hx) csup)).1 }
end

/--  The non-negative span of a basis of a vector space is pointed.
The typeclass assumptions allow the lemma to work in greater generality than what this doc-string
asserts.
For instance, this lemma applies to the `ℕ`-span of an `ℝ`-basis of a real vector space. -/
lemma pointed_of_is_basis_is_inj {ι : Type*} {v : ι → M}
  (bv : is_basis S v) (hRS : is_inj_nonneg (algebra_map R S)) :
  pointed S (submodule.span R (set.range v)) :=
begin
  obtain ⟨l, hl⟩ : ∃ l : M →ₗ[S] S, ∀ i : ι, l (v i) = 1 := ⟨bv.constr 1, λ i, constr_basis bv⟩,
  refine span_pointed_of_pos_reg_is_inj l (λ a av, _) hRS,
  rcases set.mem_range.mp av with ⟨a, rfl⟩,
  rw hl,
  exact ⟨zero_le_one, is_regular_one⟩,
end

end pairing
