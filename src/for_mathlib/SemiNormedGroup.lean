import normed_group.SemiNormedGroup

namespace SemiNormedGroup

open category_theory

universes u

-- PR'd as #7740
noncomputable instance has_zero_object : limits.has_zero_object SemiNormedGroup.{u} :=
{ zero := 0,
  unique_to := λ X,
  { default := 0,
    uniq := λ a, by { ext ⟨⟩, exact a.map_zero, }, },
  unique_from := λ X,
  { default := 0,
    uniq := λ f, by ext } }

-- Do we have this?
lemma coe_comp_apply (A B C : SemiNormedGroup) (f : A ⟶ B) (g : B ⟶ C)
  (a : A) : (f ≫ g) a = g (f a) := rfl

end SemiNormedGroup
