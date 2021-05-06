import category_theory.Fintype
import topology.category.Profinite

namespace Fintype

-- The next two lemmas can be dropped after mathlib PR #7530 hits

@[simp]
lemma id_to_fun {A : Fintype} : (𝟙 A : A → A) = id := rfl

@[simp]
lemma comp_to_fun {A B C : Fintype} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g : A → C) = g ∘ f := rfl

-- NOTE: Fintypes are given the discrete topology!
instance {A : Fintype} : topological_space A := ⊥

end Fintype

/-- The canonical functor from `Fintype` to `Profinite`. -/
def Fintype_to_Profinite : Fintype ⥤ Profinite :=
{ obj := λ A, ⟨⟨A⟩⟩,
  map := λ A B f, ⟨f⟩ }
