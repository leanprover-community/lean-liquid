import topology.category.Profinite
-- import category_theory.concrete_category

open category_theory

namespace Profinite

universe variables u

instance : concrete_category.{u u (u+1)} Profinite.{u} :=
{ forget := { obj := λ X, X, map := λ X Y f, f },
  forget_faithful := by { fsplit, intros X Y a₁ a₂ h, dsimp at *, ext1, rw h } }

@[simps hom inv]
def iso_of_homeo (X Y : Profinite) (f : X ≃ₜ Y) : X ≅ Y :=
{ hom := ⟨f, f.continuous⟩,
  inv := ⟨f.symm, f.symm.continuous⟩,
  hom_inv_id' := by { ext x, exact f.symm_apply_apply x },
  inv_hom_id' := by { ext x, exact f.apply_symm_apply x } }

/-- Construct a homeomorphism from an isomorphism. -/
def homeo_of_iso {X Y : Profinite} (f : X ≅ Y) : X ≃ₜ Y :=
{ to_fun := f.hom,
  inv_fun := f.inv,
  left_inv := λ x, by {change (f.hom ≫ f.inv) x = x, simp},
  right_inv := λx, by {change (f.inv ≫ f.hom) x = x, simp},
  continuous_to_fun := f.hom.continuous,
  continuous_inv_fun := f.inv.continuous }

end Profinite
