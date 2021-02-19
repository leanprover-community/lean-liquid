import data.polynomial.degree.lemmas
import algebra.module.ordered

variables (R₀ R M N P : Type*)

section pairing

variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [semimodule R M]
  [semimodule R N] [add_comm_monoid P] [semimodule R P]

@[derive has_coe_to_fun] def pairing := M →ₗ[R] N →ₗ[R] P

variables {R M N P}

def pairing.flip : pairing R M N P → pairing R N M P := linear_map.flip

end pairing

namespace submodule

variables {M} [comm_semiring R₀] [comm_semiring R] [algebra R₀ R] [add_comm_monoid M]
  [semimodule R₀ M] [semimodule R M] [is_scalar_tower R₀ R M]

/-- This definition does not assume that `R₀` injects into `R`.  If the map `R₀ → R` has a
non-trivial kernel, the only saturated submodule is the whole module. -/
def saturated (s : submodule R₀ M) : Prop :=
∀ (r : R₀) (hr : r ≠ 0) (m : M), r • m ∈ s → m ∈ s

def saturation (s : submodule R₀ M) : submodule R₀ M :=
{ carrier := { m : M | m = 0 ∨ ∃ (r : R₀), r ≠ 0 ∧ r • m ∈ s },
  zero_mem' := or.inl rfl,
  add_mem' := begin
    rintros a b (rfl | ra) (rfl | rb),
    { rw [add_zero],
      exact or.inl rfl },
    { rw zero_add,
      refine or.inr rb },
    { rw add_zero,
      refine or.inr ra },
    { rcases ra with ⟨ra, ra0, ras⟩,
      rcases rb with ⟨rb, rb0, rbs⟩,
      refine or.inr _,
      refine ⟨(ra * rb), mul_pos ra0 rb0, _⟩,
      rw [smul_add, mul_smul _ _ b, mul_comm ra, mul_smul],
      exact s.add_mem (s.smul_mem _ ras) (s.smul_mem _ rbs) }
  end,
   }

end submodule

namespace pairing

variables [linear_ordered_comm_ring R] [add_comm_monoid M] [add_comm_monoid N] [semimodule R M]
  [semimodule R N] [ordered_add_comm_monoid P] [semimodule R P]

variables {R M N P} (f : pairing R M N P)

def dual_set (s : set M) : submodule R N :=
{ carrier := { n : N | ∀ m ∈ s, (0 : P) ≤ f m n },
  zero_mem' := λ m hm, by simp only [linear_map.map_zero],
  add_mem' := λ n1 n2 hn1 hn2 m hm, begin
    rw linear_map.map_add,
    exact add_nonneg (hn1 m hm) (hn2 m hm)
  end }

lemma mem_dual_set (s : set M) (n : N) :
  n ∈ f.dual_set s ↔ ∀ m ∈ s, 0 ≤ f m n := iff.rfl

variables [ordered_semimodule R P]

-- move this
lemma smul_nonneg_iff (r : R) (hr : 0 < r) (p : P) :
  0 ≤ r • p ↔ 0 ≤ p :=
begin
  split,
  { intro h,

    rw le_iff_lt_or_eq at h ⊢,
    refine h.imp (smul_pos_iff_of_pos hr).mp _,
    intro hrp,
    refine eq_of_smul_eq_smul_of_pos_of_le _ hr _,
    rwa smul_zero,
    /- is this even true? do we need some extra `torsion_free` assumption here? -/
    /- we may need a "cancellable" assumption on `r`.  This feels close to the counterexample
    ordered_comm_semiring where multiplication by `2` was not injective.
    I would think about `ℤ × zmod 2` with some linear order (if it is possible, say where all the
    `(n, 1)` satisfy `(n, 0) < (n, 1) < (n + 1, 0)`) and then exploiting the fact that
    `2 • (0,1) = (0,0)`.  Maybe what I described is not a linear_ordered_comm_ring?  -/
    sorry },
  { intro h,
    simpa only [smul_zero] using smul_le_smul_of_nonneg h hr.le }
end

lemma dual_set_saturated (s : set M) : (f.dual_set s).saturated R :=
begin
  intros r hr n hn m hm,
  specialize hn m hm,
  rwa [linear_map.map_smul, smul_nonneg_iff r hr] at hn,
  apply_instance
end

lemma dual_subset {s t : set M} (st : s ⊆ t) : f.dual_set t ≤ f.dual_set s :=
λ n hn m hm, hn m (st hm)

lemma subset_dual_dual {s : set M} : s ⊆ f.flip.dual_set (f.dual_set s) :=
λ m hm _ hm', hm' m hm

lemma subset_dual_set_of_subset_dual_set {S : set M} {T : set N}
  (ST : S ⊆ f.flip.dual_set T) :
  T ⊆ f.dual_set S :=
λ n hn m hm, ST hm _ hn

lemma le_dual_set_of_le_dual_set {S : submodule R M} {T : submodule R N}
  (ST : S ≤ f.flip.dual_set T) :
  T ≤ f.dual_set S :=
subset_dual_set_of_subset_dual_set _ ST

lemma dual_set_closure_eq {s : set M} :
  f.dual_set (submodule.span R s) = f.dual_set s :=
begin
  refine le_antisymm (dual_subset _ submodule.subset_span) _,
  intros n hn m hm,
  apply submodule.span_induction hm hn,
  { simp only [linear_map.map_zero, linear_map.zero_apply] },
  { intros x y hx hy,
    simpa only [linear_map.add_apply, linear_map.map_add] using add_nonneg hx hy },
  sorry
end

/-
define saturation
dual of saturation eq dual
-/

/- flip the inequalities assuming saturatedness -/
lemma le_dual_set_of_le_dual_set_satu {S : submodule R M} {T : submodule R N}
  (ST : S ≤ f.flip.dual_set T) :
  T ≤ f.dual_set S :=
subset_dual_set_of_subset_dual_set _ ST

lemma subset_dual_set_iff {S : set M} {T : set N} :
  S ⊆ f.flip.dual_set T ↔ T ⊆ f.dual_set S :=
⟨subset_dual_set_of_subset_dual_set f, subset_dual_set_of_subset_dual_set f.flip⟩

lemma le_dual_set_iff {S : submodule R M} {T : submodule R N} :
  S ≤ f.flip.dual_set T ↔ T ≤ f.dual_set S :=
subset_dual_set_iff _

lemma dual_dual_of_saturated {S : submodule R M} (Ss : S.saturated R) :
  f.flip.dual_set (f.dual_set S) = S :=
begin
  refine le_antisymm _ (subset_dual_dual f),
  intros m hm,

  sorry,
end

end pairing
