import topology.category.Profinite.as_limit

noncomputable theory

namespace Profinite

open category_theory
open category_theory.limits

universes v u

-- Let C be a category which has enough limits.
variables {C : Type u} [category.{v} C]
  [∀ X : Profinite, has_limits_of_shape (discrete_quotient X) C]
-- And let `F` be a functor from `Fintype` to `C`.
  (F : Fintype.{v} ⥤ C)

@[simps]
def change_cone {X Y : Profinite} (f : X ⟶ Y) (D : cone (X.fintype_diagram ⋙ F)) :
  cone (Y.fintype_diagram ⋙ F) :=
{ X := D.X,
  π :=
  { app := λ S, D.π.app (S.comap f.continuous) ≫ F.map (discrete_quotient.map $ le_refl _),
    naturality' := begin
      rintros I J h,
      dsimp,
      simp only [category.id_comp, category.assoc],
      rw ← D.w (hom_of_le $ discrete_quotient.comap_mono _ $ le_of_hom h),
      simp only [category.assoc, ← F.map_comp, functor.comp_map],
      congr' 2,
      ext ⟨t⟩, refl,
    end } } .

@[simps]
def extend : Profinite ⥤ C :=
{ obj := λ X, limit (X.fintype_diagram ⋙ F),
  map := λ X Y f, limit.lift _ (change_cone _ f _),
  map_id' := begin
    intros X,
    ext S,
    dsimp,
    simp only [limit.lift_π, coe_id, change_cone_π_app, limit.cone_π, category.id_comp],
    erw discrete_quotient.map_id,
    change _ ≫ F.map (𝟙 _) = _,
    rw [F.map_id, category.comp_id],
    congr,
    exact S.comap_id,
  end,
  map_comp' := begin
    intros X Y Z f g,
    ext S,
    dsimp,
    simp only [limit.lift_π, change_cone_π_app,
      limit.cone_π, limit.lift_π_assoc, coe_comp, category.assoc, ← F.map_comp],
    congr,
    exact discrete_quotient.map_comp _ _,
  end }

end Profinite
