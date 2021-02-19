import data.polynomial.degree.lemmas
import algebra.module.ordered

variables (R M N P : Type*)

section pairing

variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [semimodule R M]
  [semimodule R N] [add_comm_monoid P] [semimodule R P]

@[derive has_coe_to_fun] def pairing := M →ₗ[R] N →ₗ[R] P

def pairing.flip : pairing R M N P → pairing R N M P := linear_map.flip

end pairing

namespace add_submonoid

variables {M} [ordered_comm_ring R] [add_comm_monoid M] [semimodule R M]

def saturated (s : add_submonoid M) : Prop :=
∀ (r : R) (hr : 0 < r) (m : M), r • m ∈ s → m ∈ s

end add_submonoid

namespace pairing

variables [ordered_comm_ring R] [add_comm_monoid M] [add_comm_monoid N] [semimodule R M]
  [semimodule R N] [ordered_add_comm_monoid P] [semimodule R P]

variables {R M N P} (f : pairing R M N P)

def dual_set (s : set M) : add_submonoid N :=
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

end pairing
