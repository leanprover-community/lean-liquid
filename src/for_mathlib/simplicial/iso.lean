import algebraic_topology.simplicial_object

open opposite category_theory category_theory.limits
open simplex_category

universes v u

namespace category_theory

namespace comma

universes v₁ v₂ v₃ u₁ u₂ u₃
variables {A : Type u₁} [category.{v₁} A]
variables {B : Type u₂} [category.{v₂} B]
variables {T : Type u₃} [category.{v₃} T]
variables {L : A ⥤ T} {R : B ⥤ T}
variables {X Y : comma L R} (f : X ⟶ Y)

lemma is_iso_of [is_iso f.left] [is_iso f.right] : is_iso f :=
{ out := ⟨
  { left := inv f.left,
    right := inv f.right,
    w' := by { dsimp,
      simp only [is_iso.eq_comp_inv, functor.map_inv, comma_morphism.w,
        is_iso.inv_comp_eq, category.assoc],
      simp } },
   by { split; ext; dsimp; simp only [is_iso.hom_inv_id, is_iso.inv_hom_id] }⟩ }

end comma

namespace simplicial_object

variables {C : Type u} [category.{v} C]

section

variables {X Y : simplicial_object C} (f : X ⟶ Y)

lemma is_iso_of [hf : ∀ n, is_iso (f.app n)] : is_iso f :=
{ out :=
  begin
    let g : Y ⟶ X :=
    { app := λ n, inv (f.app n),
      naturality' := λ m n φ, _ },
    { refine ⟨g, _, _⟩;
      { ext n,
        simp only [nat_trans.id_app, nat_trans.comp_app, is_iso.hom_inv_id, is_iso.inv_hom_id], } },
    { simp only [is_iso.inv_hom_id_assoc, nat_trans.naturality, is_iso.comp_inv_eq, category.assoc] }
  end }

end

local attribute [instance] category_theory.simplicial_object.is_iso_of

namespace augmented

variables {X Y : augmented C} (f : X ⟶ Y)

lemma is_iso_of [∀ n, is_iso (f.left.app n)] [is_iso f.right] : is_iso f :=
category_theory.comma.is_iso_of _

end augmented

end simplicial_object

end category_theory
