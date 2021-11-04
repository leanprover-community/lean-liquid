import category_theory.limits.shapes.terminal

namespace category_theory.limits

open category_theory

universes v u

variables {J : Type v} [small_category J] {C : Type u} [category.{v} C] (F : J ⥤ C)

noncomputable theory

@[simps]
def is_initial.colimit_cocone {j : J} (hj : is_initial j)
  [has_colimit F] [∀ (a b : J) (f : a ⟶ b), is_iso (F.map f)] :
  cocone F :=
{ X := F.obj j,
  ι :=
  { app := λ i, inv (F.map $ hj.to _),
    naturality' := begin
      intros a b f,
      dsimp,
      simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.comp_id],
      simp_rw ← F.map_comp,
      congr' 1,
      apply hj.hom_ext,
    end } }

def is_initial.is_colimit_colimit_cocone {j : J} (hj : is_initial j)
  [has_colimit F] [∀ (a b : J) (f : a ⟶ b), is_iso (F.map f)] :
  is_colimit (hj.colimit_cocone F) :=
{ desc := λ S, S.ι.app _ }

lemma colimit.is_iso_ι_of_forall_is_iso {j : J} (hj : is_initial j)
  [has_colimit F] [∀ (a b : J) (f : a ⟶ b), is_iso (F.map f)] :
  is_iso (colimit.ι F j) :=
begin
  let e := (colimit.is_colimit F).cocone_point_unique_up_to_iso
    (hj.is_colimit_colimit_cocone F),
  change is_iso e.inv,
  apply_instance
end

end category_theory.limits
