import topology.category.Compactum

import locally_constant.analysis
import normed_group.NormedGroup

noncomputable theory

set_option pp.proofs true

namespace NormedGroup
open opposite locally_constant

local attribute [instance] locally_constant.normed_group locally_constant.metric_space

@[simps]
def LocallyConstant : NormedGroup ⥤ CompHausᵒᵖ ⥤ NormedGroup :=
{ obj := λ V,
  { obj := λ S, NormedGroup.of $ locally_constant (unop S : CompHaus) V,
    map := λ S₁ S₂ f, comap_hom (f.unop) (f.unop.continuous),
    map_id' := λ S, comap_hom_id,
    map_comp' := λ S₁ S₂ S₃ f g, (comap_hom_comp _ _ _ _).symm },
  map := λ V W f,
  { app := λ S, map_hom f,
    naturality' := λ S₁ S₂ g,
    begin
      dsimp, ext,
      simp only [map_hom_to_fun, comap_hom_to_fun, category_theory.coe_comp,
        function.comp_app, map_apply, coe_comap, g.unop.continuous]
    end } ,
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

end NormedGroup
#lint- only unused_arguments def_lemma
