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

def change_cone {X Y : Profinite} (f : X ⟶ Y) (D : cone (X.fintype_diagram ⋙ F)) :
  cone (Y.fintype_diagram ⋙ F) :=
{ X := D.X,
  π :=
  { app := λ S, D.π.app (S.comap f.continuous) ≫ F.map (discrete_quotient.map $ le_refl _),
    naturality' := begin
      rintros I J h,
      dsimp,
      simp,
      rw ← D.w (hom_of_le $ discrete_quotient.comap_mono _ $ le_of_hom h),
      simp only [category.assoc, ← F.map_comp],
      congr' 2,
    end } }

end Profinite
