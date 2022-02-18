import topology.subset_properties
import topology.homeomorph

namespace homeomorph

variables {α β : Type*} [topological_space α] [topological_space β]
  (e : α ≃ₜ β) [totally_disconnected_space α]

include e

--TODO: Golf and add to mathlib
protected lemma totally_disconnected_space : totally_disconnected_space β :=
begin
  constructor,
  rintros A - hA,
  suffices : (e.symm '' A).subsingleton,
  { intros x hx y hy,
    apply e.symm.injective,
    apply this,
    exact ⟨x, hx, rfl⟩,
    exact ⟨y, hy, rfl⟩ },
  obtain ⟨h⟩ := (infer_instance : totally_disconnected_space α),
  apply h,
  { tauto },
  { exact is_preconnected.image hA _ e.symm.continuous.continuous_on }
end

end homeomorph
