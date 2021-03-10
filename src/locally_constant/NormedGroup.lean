import topology.category.Profinite

import locally_constant.analysis
import normed_group.NormedGroup

noncomputable theory

set_option pp.proofs true

namespace NormedGroup
open opposite locally_constant

local attribute [instance] locally_constant.normed_group locally_constant.metric_space

/-- The bifunctor of locally constant maps from profinite spaces to normed groups.
    The effects on homs of groups or space are defined in terms of push-forward
    (ie. post-composition) and pull-back (ie. pre-composition) of locally constant maps
    respectively. -/
@[simps]
def LocallyConstant : NormedGroup ⥤ Profiniteᵒᵖ ⥤ NormedGroup :=
{ obj := λ V,
  { obj := λ S, NormedGroup.of $ locally_constant (unop S : Profinite) V,
    map := λ S₁ S₂ f, comap_hom (f.unop) (f.unop.continuous),
    map_id' := λ S, comap_hom_id,
    map_comp' := λ S₁ S₂ S₃ f g, (comap_hom_comp _ _ _ _).symm },
  map := λ V W f,
  { app := λ S, map_hom f,
    naturality' := λ S₁ S₂ g,
    begin
      dsimp, ext,
      simp only [map_hom_apply, comap_hom_apply, category_theory.coe_comp,
        function.comp_app, map_apply, coe_comap, g.unop.continuous]
    end } ,
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

end NormedGroup
#lint- only unused_arguments def_lemma doc_blame
