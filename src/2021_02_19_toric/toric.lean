import data.polynomial.degree.lemmas
import algebra.module.ordered

variables (R M N P : Type*)

section pairing

variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [semimodule R M]
  [semimodule R N] [add_comm_monoid P] [semimodule R P]

@[derive has_coe_to_fun] def pairing := M →ₗ[R] N →ₗ[R] P

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

def flip : pairing R N M P := linear_map.flip f

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
  sorry
end

lemma dual_set_saturated (s : set M) : (f.dual_set s).saturated R :=
begin
  intros r hr n hn m hm,
  specialize hn m hm,
  rwa [linear_map.map_smul, smul_nonneg_iff r hr] at hn,
  apply_instance
end

end pairing
