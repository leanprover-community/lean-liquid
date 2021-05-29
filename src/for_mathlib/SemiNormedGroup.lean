import normed_group.SemiNormedGroup

-- PR'd as #7740

namespace SemiNormedGroup

open category_theory

universes u

noncomputable instance has_zero_object : limits.has_zero_object SemiNormedGroup.{u} :=
{ zero := 0,
  unique_to := λ X,
  { default := 0,
    uniq := λ a, by { ext ⟨⟩, exact a.map_zero, }, },
  unique_from := λ X,
  { default := 0,
    uniq := λ f, by ext } }

@[simp] lemma coe_comp {M N K : SemiNormedGroup} (f : M ⟶ N) (g : N ⟶ K) :
  ((f ≫ g) : M → K) = g ∘ f := rfl

end SemiNormedGroup
