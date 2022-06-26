import breen_deligne.eval

noncomputable theory

namespace category_theory
namespace preadditive
open category_theory category_theory.limits

universes v

variables {C D : Type*} [category.{v} C] [category.{v} D] [preadditive C] [preadditive D]
  [has_finite_biproducts C] [has_finite_biproducts D] (F : C ⥤ D) [functor.additive F] (n : ℕ)

@[simps]
def apply_Pow : Pow n ⋙ F ≅ F ⋙ Pow n := nat_iso.of_components (λ A,
  { hom := biproduct.lift (λ i, F.map (biproduct.π _ i)),
    inv := biproduct.desc (λ i, F.map (biproduct.ι _ i)),
    hom_inv_id' := by simpa only [biproduct.lift_desc, ← F.map_comp, ← F.map_sum,
      biproduct.total] using F.map_id _,
    inv_hom_id' := begin
      ext i j,
      by_cases i = j,
      { subst h,
        dsimp,
        simp only [biproduct.ι_desc_assoc, category.assoc, biproduct.lift_π,
          category.comp_id, biproduct.ι_π_self, ← F.map_comp, F.map_id], },
      { dsimp,
        simp only [biproduct.ι_desc_assoc, category.assoc, biproduct.lift_π,
          category.comp_id, ← F.map_comp, limits.biproduct.ι_π_ne _ h,
          functor.map_zero], },
    end, })
(λ X Y f, by { ext, simp only [category.assoc, biproduct.lift_π,
  functor.comp_map, Pow_map, biproduct.lift_map, ← F.map_comp, biproduct.map_π], })

end preadditive

end category_theory
