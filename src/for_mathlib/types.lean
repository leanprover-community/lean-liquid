import category_theory.limits.concrete_category

namespace category_theory.types

open category_theory
open category_theory.limits

universe u
variables {J : Type u} [small_category J] [is_filtered J] (F : J ⥤ Type u)

def filtered_colimit_setoid : setoid (Σ j : J, F.obj j) :=
{ r := λ x y, ∃ (e : J) (i : x.1 ⟶ e) (j : y.1 ⟶ e), F.map i x.2 = F.map j y.2,
  iseqv := begin
    refine ⟨_,_,_⟩,
    { intros x, use [x.1, 𝟙 _, 𝟙 _] },
    { rintros ⟨x,a⟩ ⟨y,b⟩ ⟨e,i,j,h⟩, use [e,j,i,h.symm] },
    { rintros ⟨x,a⟩ ⟨y,b⟩ ⟨z,c⟩ ⟨e₁,i₁,j₁,h₁⟩ ⟨e₂,i₂,j₂,h₂⟩,
      let e₀ := is_filtered.max e₁ e₂, dsimp at *,
      let e := is_filtered.coeq (j₁ ≫ is_filtered.left_to_max e₁ e₂)
        (i₂ ≫ is_filtered.right_to_max e₁ e₂),
      let t : e₀ ⟶ e := is_filtered.coeq_hom _ _,
      use e,
      use i₁ ≫ is_filtered.left_to_max _ _ ≫ t,
      use j₂ ≫ is_filtered.right_to_max _ _ ≫ t,
      simp only [←h₂, h₁, functor_to_types.map_comp_apply],
      -- This is really annoying...
      change (F.map _ ≫ F.map _ ≫ F.map _) _ =
        (F.map _ ≫ F.map _ ≫ F.map _) _,
      dsimp only [t],
      simp only [← F.map_comp, ← category.assoc, is_filtered.coeq_condition] }
  end }

def filtered_colimit_cocone : cocone F :=
{ X := quotient (filtered_colimit_setoid F),
  ι :=
  { app := λ j t, quotient.mk' ⟨j,t⟩,
    naturality' := begin
      intros i j f, ext, dsimp, apply quotient.sound',
      use [j, 𝟙 _, f], simp,
    end } }

def filtered_colimit_cocone_is_colimit (F : J ⥤ Type u) :
  is_colimit (filtered_colimit_cocone F) :=
{ desc := λ S, λ t,
    -- ARRGH
    @quotient.lift_on' (Σ (j : J), F.obj j) S.X _ t (λ x, S.ι.app x.1 x.2) begin
      rintros ⟨i,a⟩ ⟨j,b⟩ ⟨e,f,g,h⟩, dsimp at *,
      rw ← S.w f, rw ← S.w g, simp only [types_comp_apply, h],
    end,
  fac' := λ S j, by { ext, refl },
  uniq' := begin
    intros S m hm, ext ⟨⟨i,t⟩⟩, specialize hm i,
    apply_fun (λ e, e t) at hm, exact hm,
  end }

end category_theory.types
