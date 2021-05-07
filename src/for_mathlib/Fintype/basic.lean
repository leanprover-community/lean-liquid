import category_theory.Fintype
import topology.category.Profinite

namespace Fintype

-- NOTE: Fintypes are given the discrete topology!
instance {A : Fintype} : topological_space A := ⊥

end Fintype

/-- The canonical functor from `Fintype` to `Profinite`. -/
def Fintype_to_Profinite : Fintype ⥤ Profinite :=
{ obj := λ A, ⟨⟨A⟩⟩,
  map := λ A B f, ⟨f⟩ }
