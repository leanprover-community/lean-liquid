import data.polynomial.degree.lemmas

variables (R M N P : Type*)

section pairing

variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [semimodule R M]
  [semimodule R N] [add_comm_monoid P] [semimodule R P]

@[derive has_coe_to_fun] def pairing := M →ₗ[R] N →ₗ[R] P

end pairing

namespace pairing

variables [ordered_comm_ring R]

variables [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N]
  [linear_ordered_add_comm_group P] [semimodule R P]

variable (f : pairing R M N P)

def flip : pairing R N M P := linear_map.flip f

def dual_set (s : set M) : add_submonoid N :=
{ carrier := { n : N | ∀ m ∈ s, (0 : P) ≤ f m n },
  zero_mem' := λ m hm, by simp only [linear_map.map_zero],
  add_mem' := λ n1 n2 hn1 hn2 m hm, begin
    rw linear_map.map_add,
    exact add_nonneg (hn1 m hm) (hn2 m hm)
  end }


end pairing
