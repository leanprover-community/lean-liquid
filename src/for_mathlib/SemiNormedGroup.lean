import normed_group.SemiNormedGroup

namespace SemiNormedGroup

open category_theory

universes u

noncomputable instance has_zero_object : limits.has_zero_object SemiNormedGroup.{u} :=
{ zero := 0,
  unique_to := λ X,
  { default := 0,
    uniq := begin
      intros a,
      dsimp [default],
      ext x,
      have : x = 0, by dec_trivial,
      rw this,
      rw a.map_zero,
      simp [a.map_zero],
    end },
  unique_from := λ X,
  { default := 0,
    uniq := begin
      intros f,
      dsimp [default],
      ext x,
    end } }

-- Do we have this?
lemma coe_comp_apply (A B C : SemiNormedGroup) (f : A ⟶ B) (g : B ⟶ C)
  (a : A) : (f ≫ g) a = g (f a) := rfl

end SemiNormedGroup
