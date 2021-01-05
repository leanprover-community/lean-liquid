import topology.constructions

def type_pow : has_pow (Type*) ℕ := ⟨λ A n, fin n → A⟩

namespace type_pow_topology

local attribute [instance] type_pow

instance topological_space {n : ℕ} {α : Type*} [topological_space α] : topological_space (α^n) :=
  Pi.topological_space

--instance {n : ℕ} {α : Type*} [topological_space α] [discrete_topology α] : discrete_topology (α^n) := sorry

end type_pow_topology
