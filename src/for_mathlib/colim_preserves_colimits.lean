import category_theory.limits.functor_category
import category_theory.limits.preserves.basic
import tactic.apply_fun

open category_theory
namespace category_theory.limits

universes v u
variables (J : Type v) [small_category J] (C : Type u)
  [category.{v} C] [has_colimits C]

noncomputable
def is_colimit_colim_map_cocone
  {K : Type v} [small_category K]
  (F: K ⥤ J ⥤ C)
  (T: limits.cocone F)
  (hT: limits.is_colimit T) :
  limits.is_colimit (limits.colim.map_cocone T) :=
{ desc := λ S, colimit.desc T.X ⟨S.X,
  { app := λ j, (is_colimit_of_preserves ((evaluation J C).obj j) hT).desc ⟨S.X,
    { app := λ k,
        by apply limits.colimit.ι (F.obj k) j ≫ S.ι.app k,
      naturality' := begin
        intros k₁ k₂ f,
        dsimp,
        simp [← S.w f],
      end }⟩,
    naturality' := begin
      intros j₁ j₂ f,
      apply (limits.is_colimit_of_preserves ((evaluation J C).obj j₁) hT).hom_ext, intros k,
      dsimp,
      simp only [category.comp_id],
      erw (limits.is_colimit_of_preserves ((evaluation J C).obj j₁) hT).fac,
      rw ← nat_trans.naturality_assoc,
      erw (limits.is_colimit_of_preserves ((evaluation J C).obj j₂) hT).fac,
      simp,
    end }⟩,
  fac' := begin
    intros S k,
    ext j, dsimp,
    simp only [colimit.map_desc, colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app],
    apply (limits.is_colimit_of_preserves ((evaluation J C).obj j) hT).fac,
  end,
  uniq' := begin
    intros S m hm,
    ext j,
    simp only [colimit.ι_desc],
    apply (limits.is_colimit_of_preserves ((evaluation J C).obj j) hT).hom_ext, intros k,
    dsimp,
    specialize hm k,
    dsimp at hm,
    apply_fun (λ e, colimit.ι _ j ≫ e) at hm,
    simp only [colimit.ι_map_assoc] at hm,
    rw [hm],
    erw (limits.is_colimit_of_preserves ((evaluation J C).obj j) hT).fac,
  end }

noncomputable
instance colim_preserves_colimits : preserves_colimits (colim : (J ⥤ C) ⥤ C) :=
begin
  constructor,
  introsI K hK, constructor,
  intros F,
  constructor,
  intros T hT,
  apply is_colimit_colim_map_cocone,
  assumption
end

end category_theory.limits
