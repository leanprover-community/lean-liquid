import topology.category.Profinite
import category_theory.filtered

import locally_constant.analysis
import normed_group.NormedGroup

/-!

# The functor of locally constant maps

The functor sending a normed group `V` and a profinite type `S` to the normed group
of locally constant maps from `S` to `V` (with the sup norm).

## Main definition

- `LocallyConstant : NormedGroup ⥤ Profiniteᵒᵖ ⥤ NormedGroup` : the functor.

-/

noncomputable theory

set_option pp.proofs true

namespace NormedGroup
open opposite locally_constant

local attribute [instance] locally_constant.semi_normed_group locally_constant.pseudo_metric_space

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

lemma LocallyConstant_obj_map_norm_noninc (V : NormedGroup) (X Y : Profiniteᵒᵖ) (φ : X ⟶ Y) :
  ((LocallyConstant.obj V).map φ).norm_noninc :=
comap_hom_norm_noninc _ _

open category_theory

universe u

instance {M : NormedGroup.{u}} {J : Type u} [small_category J] [is_filtered J] :
  limits.preserves_colimits_of_shape J (LocallyConstant.obj M) := sorry

end NormedGroup
#lint- only unused_arguments def_lemma doc_blame
