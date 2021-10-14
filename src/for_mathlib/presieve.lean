import category_theory.sites.sheaf

open category_theory opposite

universes w v u v' u'

variables {C : Type u} [category.{v} C]

namespace category_theory.presieve

lemma mem_of_arrows_iff {ι} {B Y} (X : ι → C) (f : Π i, X i ⟶ B) (g : Y ⟶ B) :
  of_arrows X f g ↔ ∃ (i : ι) (hi : Y = X i), g = eq_to_hom hi ≫ f i :=
begin
  split,
  { rintros ⟨i⟩,
    use [i, rfl],
    simp },
  { rintros ⟨i,rfl,rfl⟩,
    simp [of_arrows.mk i] }
end

end category_theory.presieve
