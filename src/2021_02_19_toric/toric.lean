import data.polynomial.degree.lemmas
import algebra.module.ordered
import algebra.regular

variables (R₀ R M N P : Type*)

variables [comm_semiring R₀] [comm_semiring R] [algebra R₀ R]
  [add_comm_monoid M] [semimodule R₀ M] [semimodule R M] [is_scalar_tower R₀ R M]
  [add_comm_monoid N] [semimodule R₀ N] [semimodule R N] [is_scalar_tower R₀ R N]
  [add_comm_monoid P] [semimodule R₀ P] [semimodule R P] [is_scalar_tower R₀ R P]
  (P₀ : submodule R₀ P)
section pairing


/-- An R-pairing on the R-modules M, N, P is an R-linear map M -> Hom_R(N,P). -/
@[derive has_coe_to_fun] def pairing := M →ₗ[R] N →ₗ[R] P

variables {R M N P}

def pairing.flip : pairing R M N P → pairing R N M P := linear_map.flip

end pairing

variables {M}

namespace submodule

/-- This definition does not assume that `R₀` injects into `R`.  If the map `R₀ → R` has a
non-trivial kernel, this might not be the definition you think. -/
def saturated (s : submodule R₀ M) : Prop :=
∀ (r : R₀) (hr : is_regular r) (m : M), r • m ∈ s → m ∈ s

def saturation (s : submodule R₀ M) : submodule R₀ M :=
{ carrier := { m : M | ∃ (r : R₀), is_regular r ∧ r • m ∈ s },
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
  smul_mem' := begin
    rintros c m ⟨r, hrreg, hrm⟩,
    use [r, hrreg],
    rw smul_algebra_smul_comm,
    exact s.smul_mem _ hrm,
  end }

lemma le_saturation (s : submodule R₀ M) : s ≤ saturation R₀ s :=
λ m hm, ⟨1, is_regular_one, by rwa one_smul⟩

/- I (DT) extracted this lemma from the proof of `dual_eq_dual_saturation`, since it seems a
lemma that we may use elsewhere as well. -/
lemma set_subset_saturation  {S : set M} :
  S ⊆ (submodule.saturation R₀ (submodule.span R₀ S)) :=
set.subset.trans (submodule.subset_span : S ⊆ submodule.span R₀ S)
  (submodule.le_saturation R₀ (submodule.span R₀ S))

end submodule

namespace pairing

variables {R₀ R M N P} (f : pairing R M N P)

def dual_set (s : set M) : submodule R₀ N :=
{ carrier := { n : N | ∀ m ∈ s, f m n ∈ P₀ },
  zero_mem' := λ m hm, by simp only [linear_map.map_zero, P₀.zero_mem],
  add_mem' := λ n1 n2 hn1 hn2 m hm, begin
    rw linear_map.map_add,
    exact P₀.add_mem (hn1 m hm) (hn2 m hm),
  end,
  smul_mem' := begin
    rintro r n h m hms,
    simp [h m hms, P₀.smul_mem],
  end
}

lemma mem_dual_set (s : set M) (n : N) :
  n ∈ f.dual_set P₀ s ↔ ∀ m ∈ s, f m n ∈ P₀ := iff.rfl

section saturated

variables {P₀} (hP₀ : P₀.saturated R₀)
include hP₀

lemma smul_regular_iff {r : R₀} (hr : is_regular r) (p : P) :
  r • p ∈ P₀ ↔ p ∈ P₀ :=
⟨hP₀ _ hr _, P₀.smul_mem _⟩

lemma dual_set_saturated (s : set M) (hP₀ : P₀.saturated R₀) :
  (f.dual_set P₀ s).saturated R₀ :=
λ r hr n hn m hm, by simpa [smul_regular_iff hP₀ hr] using hn m hm

end saturated

-- this instance is missing -- see forthcoming PR by KMB 20/02/21
instance : is_scalar_tower R₀ R (N →ₗ[R] P) :=
{ smul_assoc := λ _ _ _, linear_map.ext $ by simp }

variable {P₀}

lemma dual_subset {s t : set M} (st : s ⊆ t) : f.dual_set P₀ t ≤ f.dual_set P₀ s :=
λ n hn m hm, hn m (st hm)

lemma mem_span_dual_set (s : set M) :
  f.dual_set P₀ (submodule.span R₀ s) = f.dual_set P₀ s :=
begin
  refine (dual_subset f submodule.subset_span).antisymm _,
  { refine λ n hn m hm, submodule.span_induction hm hn _ _ _,
    { simp only [linear_map.map_zero, submodule.zero_mem, linear_map.zero_apply] },
    { exact λ x y hx hy, by simp [P₀.add_mem hx hy] },
    { exact λ r m hm, by simp [P₀.smul_mem _ hm] } }
end

lemma subset_dual_dual {s : set M} : s ⊆ f.flip.dual_set P₀ (f.dual_set P₀ s) :=
λ m hm _ hm', hm' m hm

lemma subset_dual_set_of_subset_dual_set {S : set M} {T : set N}
  (ST : S ⊆ f.flip.dual_set P₀ T) :
  T ⊆ f.dual_set P₀ S :=
λ n hn m hm, ST hm _ hn

lemma le_dual_set_of_le_dual_set {S : submodule R₀ M} {T : submodule R₀ N}
  (ST : S ≤ f.flip.dual_set P₀ T) :
  T ≤ f.dual_set P₀ S :=
subset_dual_set_of_subset_dual_set _ ST

lemma dual_set_closure_eq {s : set M} :
  f.dual_set P₀ (submodule.span R₀ s) = f.dual_set P₀ s :=
begin
  refine (dual_subset _ submodule.subset_span).antisymm _,
  refine λ n hn m hm, submodule.span_induction hm hn _ _ _,
  { simp only [linear_map.map_zero, linear_map.zero_apply, P₀.zero_mem] },
  { exact λ x y hx hy, by simp only [linear_map.add_apply, linear_map.map_add, P₀.add_mem hx hy] },
  { exact λ r m hmn, by simp [P₀.smul_mem r hmn] },
end

lemma dual_eq_dual_saturation {S : set M} (hP₀ : P₀.saturated R₀) :
  f.dual_set P₀ S = f.dual_set P₀ ((submodule.span R₀ S).saturation R₀) :=
begin
  refine le_antisymm _ (dual_subset _ (submodule.set_subset_saturation R₀)),
  rintro n hn m ⟨r, hr_reg, hrm⟩,
  refine (smul_regular_iff hP₀ hr_reg _).mp _,
  rw [← mem_span_dual_set, mem_dual_set] at hn,
  simpa using hn (r • m) hrm
end

/- flip the inequalities assuming saturatedness -/
lemma le_dual_set_of_le_dual_set_satu {S : submodule R₀ M} {T : submodule R₀ N}
  (ST : S ≤ f.flip.dual_set P₀ T) :
  T ≤ f.dual_set P₀ S :=
subset_dual_set_of_subset_dual_set _ ST

lemma subset_dual_set_iff {S : set M} {T : set N} :
  S ⊆ f.flip.dual_set P₀ T ↔ T ⊆ f.dual_set P₀ S :=
⟨subset_dual_set_of_subset_dual_set f, subset_dual_set_of_subset_dual_set f.flip⟩

lemma le_dual_set_iff {S : submodule R₀ M} {T : submodule R₀ N} :
  S ≤ f.flip.dual_set P₀ T ↔ T ≤ f.dual_set P₀ S :=
subset_dual_set_iff _

/- This lemma is a weakining of the next one.  It has the advantage that we can prove it in
this level of generality!  ;)
-/
lemma dual_dual_dual_of_saturated {S : submodule R₀ M} (Ss : S.saturated R₀) :
  f.dual_set P₀ (f.flip.dual_set P₀ (f.dual_set P₀ S)) = f.dual_set P₀ S :=
le_antisymm (λ m hm n hn, hm _ ((le_dual_set_iff f).mpr rfl.le hn)) (λ m hm n hn, hn m hm)

lemma dual_dual_of_saturated {S : submodule R₀ M} (Ss : S.saturated R₀) :
  f.flip.dual_set P₀ (f.dual_set P₀ S) = S :=
begin
  refine le_antisymm _ (subset_dual_dual f),
  intros m hm,
--  rw mem_dual_set at hm,
  change ∀ (n : N), n ∈ (dual_set P₀ f ↑S) → f m n ∈ P₀ at hm,
  simp_rw mem_dual_set at hm,
  -- is this true? I (KMB) don't know and the guru (Damiano) has left!
  -- oh wait, no way is this true, we need some nondegeneracy condition
  -- on f, it's surely not true if f is just the zero map.
  -- I (DT) think that you are right, Kevin.  We may now start to make assumptions
  -- that are more specific to our situation.
  sorry,
end


end pairing
