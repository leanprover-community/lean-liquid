import category_theory.arrow
import category_theory.with_terminal

namespace category_theory

universes v u

variables {C : Type u} [category.{v} C]

local attribute [tidy] tactic.case_bash

@[simps]
def from_arrow : arrow C ⥤ ((with_terminal (discrete (punit : Type v))) ⥤ C) :=
{ obj := λ f, with_terminal.lift (discrete.functor (λ _, f.left)) (λ _, f.hom) $
    by {rintros ⟨⟩ ⟨⟩ ⟨⟩, simp},
  map := λ f g ff,
  { app := λ x,
      match x with
      | with_terminal.of punit.star := ff.left
      | with_terminal.star := ff.right
      end,
    naturality' := begin
      rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩; dsimp [with_terminal.lift, discrete.functor],
      any_goals { erw [category.id_comp, category.comp_id] },
      { erw ff.w, refl },
    end } }.

@[simps]
def to_arrow : ((with_terminal (discrete (punit : Type v))) ⥤ C) ⥤ arrow C :=
{ obj := λ F, arrow.mk $ F.map (with_terminal.hom_from punit.star),
  map := λ F G η,
  { left := η.app _,
    right := η.app _ } }.

@[simps]
def arrow_unit_iso : 𝟭 (arrow C) ≅ from_arrow ⋙ to_arrow :=
{ hom :=
  { app := λ ff,
    { left := 𝟙 _,
      right := 𝟙 _ } },
  inv :=
  { app := λ ff,
    { left := 𝟙 _,
      right := 𝟙 _ } },
  --hom_inv_id' := _,
  --inv_hom_id' := _
  }.

--local attribute [-tidy] tactic.case_bash

@[simps]
def arrow_counit_iso : (to_arrow : _ ⥤ arrow C) ⋙ from_arrow ≅ 𝟭 _ :=
{ hom :=
  { app := λ F,
    { app := λ x,
      match x with
      | with_terminal.of punit.star := 𝟙 _
      | with_terminal.star := 𝟙 _
      end,
      naturality' := begin
        rintro (⟨⟨⟩⟩|⟨⟩) (⟨⟨⟩⟩|⟨⟩) (⟨⟩|⟨⟩),
        any_goals {erw category.id_comp},
        any_goals {erw functor.map_id},
        any_goals {erw category.comp_id},
        any_goals {refl},
      end },
    naturality' := begin
      intros F G η,
      ext (⟨⟨⟩⟩|⟨⟩),
      --any_goals { sorry },
      tidy,
    end },
  inv :=
  { app := λ F,
    { app := λ x,
      match x with
      | with_terminal.of punit.star := 𝟙 _
      | with_terminal.star := 𝟙 _
      end,
      naturality' := begin
        rintros (⟨⟨⟩⟩|⟨⟩) (⟨⟨⟩⟩|⟨⟩) (⟨⟩|⟨⟩),
        any_goals {erw category.id_comp},
        any_goals {erw functor.map_id},
        any_goals {erw category.comp_id},
        any_goals {refl},
      end },
    naturality' := begin
      intros F G η,
      ext (⟨⟨⟩⟩|⟨⟩),
      --any_goals { sorry },
      tidy,
    end },
  hom_inv_id' := begin
    ext F (⟨⟨⟩⟩|⟨⟩),
    any_goals { simp only [category_theory.nat_trans.comp_app, category_theory.nat_trans.id_app],
      erw category.id_comp,
      refl },
  end,
  inv_hom_id' := begin
    ext F (⟨⟨⟩⟩|⟨⟩),
    any_goals { simp only [category_theory.nat_trans.comp_app, category_theory.nat_trans.id_app],
      erw category.id_comp,
      refl },
  end }.

@[simps]
def arrow_equiv : arrow C ≌ ((with_terminal (discrete (punit : Type v))) ⥤ C) :=
{ functor := from_arrow,
  inverse := to_arrow,
  unit_iso := arrow_unit_iso,
  counit_iso := arrow_counit_iso,
  functor_unit_iso_comp' := begin
    rintro ⟨fl,fr,f⟩,
    ext (⟨⟨⟩⟩|⟨⟩); dsimp,
    any_goals {
      erw category.id_comp,
      refl},
  end }

end category_theory
