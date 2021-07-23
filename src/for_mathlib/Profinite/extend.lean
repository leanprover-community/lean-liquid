import topology.category.Profinite.as_limit
import for_mathlib.discrete_quotient
import for_mathlib.Fintype

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
  end } .

@[simps]
def bot_initial (X : Fintype) :
  is_initial (⊥ : discrete_quotient (Fintype.to_Profinite.obj X)) :=
{ desc := λ S, hom_of_le bot_le }

@[simps]
def extend_extends : Fintype.to_Profinite ⋙ extend F ≅ F :=
nat_iso.of_components (λ X, begin
  dsimp only [extend, functor.comp_obj],
  let Y := Fintype.to_Profinite.obj X,
  let D := limit.is_limit (Y.fintype_diagram ⋙ F),
  let E := limit_of_diagram_initial (bot_initial X) (Y.fintype_diagram ⋙ F),
  letI : topological_space X := ⊥,
  let e : Fintype.of (⊥ : discrete_quotient X) ≅ X :=
    Fintype.iso_of_equiv (equiv.of_bijective _ (discrete_quotient.proj_bot_bijective _)).symm,
  let g := D.cone_point_unique_up_to_iso E,
  exact g ≪≫ F.map_iso e,
end) begin
  intros X Y f,
  letI : topological_space X := ⊥,
  letI : topological_space Y := ⊥,
  have hf : continuous f := continuous_bot,
  let A := Fintype.to_Profinite.obj X,
  let B := Fintype.to_Profinite.obj Y,
  dsimp [is_limit.cone_point_unique_up_to_iso, limit_of_diagram_initial],
  simp only [change_cone_π_app, limit.cone_π, limit.lift_π_assoc, category.assoc],
  let e : (⊥ : discrete_quotient X) ⟶ (⊥ : discrete_quotient Y).comap hf :=
    hom_of_le bot_le,
  erw ← limit.w (A.fintype_diagram ⋙ F) e,
  simp only [category.assoc, ← F.map_comp, functor.comp_map],
  congr' 2,
  simp_rw [← iso.inv_comp_eq, ← category.assoc],
  symmetry,
  rw ← iso.comp_inv_eq,
  refl,
end


end Profinite
