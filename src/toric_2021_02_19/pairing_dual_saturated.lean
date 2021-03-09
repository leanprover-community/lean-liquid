--import toric_2021_02_19.toric
import algebra.regular
import linear_algebra.finite_dimensional

variables (R S M : Type*)
variables [comm_semiring R] [add_comm_monoid M] [semimodule R M]

section saturation

namespace submodule

section comm_semiring

variables {R} {M}

/-- This definition does not assume that `R` injects into `S`.  If the map `R → S` has a
non-trivial kernel, this might not be the definition you think. -/
def saturated (s : submodule R M) : Prop :=
∀ (r : R) (hr : is_regular r) (m : M), r • m ∈ s → m ∈ s

/--  The saturation of a submodule `s ⊆ M` is the submodule obtained from `s` by adding all
elements of `M` that admit a multiple by a regular element of `R` lying in `s`. -/
def saturation (s : submodule R M) : submodule R M :=
{ carrier := { m : M | ∃ (r : R), is_regular r ∧ r • m ∈ s },
  zero_mem' := ⟨1, is_regular_one, by { rw smul_zero, exact s.zero_mem }⟩,
  add_mem' := begin
    rintros a b ⟨q, hqreg, hqa⟩ ⟨r, hrreg, hrb⟩,
    refine ⟨q * r, is_regular_mul_iff.mpr ⟨hqreg, hrreg⟩, _⟩,
    rw [smul_add],
    refine s.add_mem _ _,
    { rw [mul_comm, mul_smul],
      exact s.smul_mem _ hqa },
    { rw mul_smul,
      exact s.smul_mem _ hrb },
  end,
  smul_mem' := λ c m ⟨r, hrreg, hrm⟩,
    ⟨r, hrreg, by {rw smul_algebra_smul_comm, exact s.smul_mem _ hrm}⟩ }

/--  The saturation of `s` contains `s`. -/
lemma le_saturation (s : submodule R M) : s ≤ saturation s :=
λ m hm, ⟨1, is_regular_one, by rwa one_smul⟩

/-- The set `S` is contained in the saturation of the submodule spanned by `S` itself. -/
lemma set_subset_saturation  {s : set M} :
  s ⊆ (submodule.saturation (submodule.span R s)) :=
set.subset.trans (submodule.subset_span : s ⊆ submodule.span R s)
  (submodule.le_saturation (submodule.span R s))

/-
WIP
lemma reg_smul_sat_of_sat {s : set M} {a : R} (ra : is_regular a) :
  saturation (span R s) = saturation (span R (a • s)) :=
begin
  ext m,
  refine ⟨_, _⟩; intros h,
  apply (mem_carrier _).mp,
  apply set.mem_of_mem_of_subset ((mem_carrier _).mp h) _,
  intros n hn,
  rintros r hr m rmas t ⟨⟨Hc, H0, Hadd, Hsmul⟩, rfl⟩,
  rintros t ⟨H, rfl⟩,
  dsimp at *,
  unfold saturated at sat,
  obtain F : m ∈ span R (a • s) := sat r hr _ rmas,
  library_search,
end

lemma reg_smul_sat_of_sat {s : set M} {a : R} (ra : is_regular a) (sat : saturated (span R s)) :
  saturated (span R (a • s)) :=
begin
  rintros r hr m rmas t ⟨⟨Hc, H0, Hadd, Hsmul⟩, rfl⟩,
  rintros t ⟨H, rfl⟩,
  dsimp at *,
  unfold saturated at sat,
  obtain F : m ∈ span R (a • s) := sat r hr _ rmas,
  library_search,
end
-/

end comm_semiring

lemma saturated_of_field [field S] [semimodule S M] (s : submodule S M) : saturated s :=
begin
  intros r hr m rms,
  rw [← one_smul S m, ← @inv_mul_cancel _ _ r, ← smul_eq_mul, smul_assoc],
  exact smul_mem s r⁻¹ rms,
  rintro rfl,
  haveI nt : nontrivial S := by apply_instance,
  exact (not_nontrivial_iff_subsingleton.mpr (is_left_regular_zero_iff_subsingleton.mp hr.left)) nt,
end

end submodule

end saturation

section pairing

variables [comm_semiring S] [algebra R S] [semimodule S M] [is_scalar_tower R S M]

variables (N P : Type*)
  [add_comm_monoid N] [semimodule R N] [semimodule S N] [is_scalar_tower R S N]
  [add_comm_monoid P] [semimodule R P] [semimodule S P] [is_scalar_tower R S P]
  (P₀ : submodule R P)

/-- An R-pairing on the R-modules M, N, P is an R-linear map M -> Hom_R(N,P). -/
@[derive has_coe_to_fun] def pairing := M →ₗ[S] N →ₗ[S] P

namespace pairing

instance inhabited : inhabited (pairing S M N P) :=
⟨{to_fun := 0, map_add' := by simp, map_smul' := by simp }⟩

variables {R S M N P}

/--  Given a pairing between the `R`-modules `M` and `N`, we obtain a pairing between `N` and `M`
by exchanging the factors. -/
def flip : pairing S M N P → pairing S N M P := linear_map.flip

variables (f : pairing S M N P)

/-- For a given pairing `<_, _> : M × N → P` and an element `m ∈ M`, `mul_left` is the linear map
`n ↦ <m, n>`.
-- Left multiplication may not be needed.
def mul_left (m : M) : N →ₗ[R] P :=
{ to_fun := λ n, f m n,
  map_add' := λ x y, by simp only [linear_map.add_apply, linear_map.map_add],
  map_smul' := λ x y, by simp only [linear_map.smul_apply, linear_map.map_smul] }

/-- For a given pairing `<_, _> : M × N → P` and an element `n ∈ N`, `mul_right` is the linear map
`m ↦ <m, n>`. -/
def mul_right (n : N) : M →ₗ[R] P :=
{ to_fun := λ m, f m n,
  map_add' := λ x y, by simp only [linear_map.add_apply, linear_map.map_add],
  map_smul' := λ x y, by simp only [linear_map.smul_apply, linear_map.map_smul] }
-/

example {n : N} : f.flip n = f.flip n := rfl

/--  A pairing `M × N → P` is `left_nondegenerate` if `0 ∈ N` is the only element of `N` pairing
to `0` with all elements of `M`. -/
def left_nondegenerate : Prop := ∀ n : N, (∀ m : M, f m n = 0) → n = 0

/--  A pairing `M × N → P` is `right_nondegenerate` if `0 ∈ M` is the only element of `M` pairing
to `0` with all elements of `N`. -/
def right_nondegenerate : Prop := ∀ m : M, (∀ n : N, f m n = 0) → m = 0

/--  A pairing `M × N → P` is `perfect` if it is left and right nondegenerate. -/
def perfect : Prop := left_nondegenerate f ∧ right_nondegenerate f

/--  For a subset `s ⊆ M`, the `dual_set s` is the submodule consisting of all elements of `N`
that have "positive pairing with all the elements of `s`.  "Positive" means that it lies in the
`R`-submodule `P₀` of `P`. -/
def dual_set (s : set M) : submodule R N :=
{ carrier := { n : N | ∀ m ∈ s, f m n ∈ P₀ },
  zero_mem' := λ m hm, by simp only [linear_map.map_zero, P₀.zero_mem],
  add_mem' := λ n1 n2 hn1 hn2 m hm, begin
    rw linear_map.map_add,
    exact P₀.add_mem (hn1 m hm) (hn2 m hm),
  end,
  smul_mem' := λ r n h m hms, by simp [h m hms, P₀.smul_mem] }

lemma mem_dual_set (s : set M) (n : N) :
  n ∈ f.dual_set P₀ s ↔ ∀ m ∈ s, f m n ∈ P₀ := iff.rfl

section saturated

variables {P₀} (hP₀ : P₀.saturated)
include hP₀

lemma smul_regular_iff {r : R} (hr : is_regular r) (p : P) :
  r • p ∈ P₀ ↔ p ∈ P₀ :=
⟨hP₀ _ hr _, P₀.smul_mem _⟩

lemma dual_set_saturated (s : set M) (hP₀ : P₀.saturated) :
  (f.dual_set P₀ s).saturated :=
λ r hr n hn m hm, by simpa [smul_regular_iff hP₀ hr] using hn m hm

end saturated

variable {P₀}

lemma dual_subset {s t : set M} (st : s ⊆ t) : f.dual_set P₀ t ≤ f.dual_set P₀ s :=
λ n hn m hm, hn m (st hm)

lemma mem_span_dual_set (s : set M) :
  f.dual_set P₀ (submodule.span R s) = f.dual_set P₀ s :=
begin
  refine (dual_subset f submodule.subset_span).antisymm _,
  { refine λ n hn m hm, submodule.span_induction hm hn _ _ _,
    { simp only [linear_map.map_zero, submodule.zero_mem, linear_map.zero_apply] },
    { exact λ x y hx hy, by simp [P₀.add_mem hx hy] },
    { exact λ r m hm, by simp [P₀.smul_mem _ hm] } }
end

lemma subset_dual_dual {s : set M} : s ⊆ f.flip.dual_set P₀ (f.dual_set P₀ s) :=
λ m hm _ hm', hm' m hm

lemma subset_dual_set_of_subset_dual_set {s : set M} {t : set N}
  (st : s ⊆ f.flip.dual_set P₀ t) :
  t ⊆ f.dual_set P₀ s :=
λ n hn m hm, st hm _ hn

lemma le_dual_set_of_le_dual_set {s : submodule R M} {t : submodule R N}
  (st : s ≤ f.flip.dual_set P₀ t) :
  t ≤ f.dual_set P₀ s :=
subset_dual_set_of_subset_dual_set _ st

lemma dual_set_closure_eq {s : set M} :
  f.dual_set P₀ (submodule.span R s) = f.dual_set P₀ s :=
begin
  refine (dual_subset _ submodule.subset_span).antisymm _,
  refine λ n hn m hm, submodule.span_induction hm hn _ _ _,
  { simp only [linear_map.map_zero, linear_map.zero_apply, P₀.zero_mem] },
  { exact λ x y hx hy, by simp only [linear_map.add_apply, linear_map.map_add, P₀.add_mem hx hy] },
  { exact λ r m hmn, by simp [P₀.smul_mem r hmn] },
end

lemma dual_eq_dual_saturation {s : set M} (hP₀ : P₀.saturated) :
  f.dual_set P₀ s = f.dual_set P₀ ((submodule.span R s).saturation) :=
begin
  refine le_antisymm _ (dual_subset _ (submodule.set_subset_saturation)),
  rintro n hn m ⟨r, hr_reg, hrm⟩,
  refine (smul_regular_iff hP₀ hr_reg _).mp _,
  rw [← mem_span_dual_set, mem_dual_set] at hn,
  simpa using hn (r • m) hrm
end

/- flip the inequalities assuming saturatedness -/
lemma le_dual_set_of_le_dual_set_satu {s : submodule R M} {t : submodule R N}
  (st : s ≤ f.flip.dual_set P₀ t) :
  t ≤ f.dual_set P₀ s :=
subset_dual_set_of_subset_dual_set _ st

lemma subset_dual_set_iff {s : set M} {t : set N} :
  s ⊆ f.flip.dual_set P₀ t ↔ t ⊆ f.dual_set P₀ s :=
⟨subset_dual_set_of_subset_dual_set f, subset_dual_set_of_subset_dual_set f.flip⟩

lemma le_dual_set_iff {s : submodule R M} {t : submodule R N} :
  s ≤ f.flip.dual_set P₀ t ↔ t ≤ f.dual_set P₀ s :=
subset_dual_set_iff _

/- This lemma is a weakining of `dual_dual_of_saturated`.
It has the advantage that we can prove it in this level of generality!  ;) -/
lemma dual_dual_dual (s : set M) :
  f.dual_set P₀ (f.flip.dual_set P₀ (f.dual_set P₀ s)) = f.dual_set P₀ s :=
le_antisymm (λ m hm n hn, hm _ ((subset_dual_set_iff f).mpr set.subset.rfl hn))
  (λ m hm n hn, hn m hm)

variable (P₀)

open submodule

end pairing

end pairing
