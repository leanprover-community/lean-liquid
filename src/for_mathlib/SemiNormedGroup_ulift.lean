import algebra.group.ulift

import for_mathlib.SemiNormedGroup

import normed_group.normed_with_aut

universes v u

namespace semi_normed_group

variables (V : Type u) [semi_normed_group V]

instance : semi_normed_group (ulift.{v} V) :=
@semi_normed_group.induced V _ (ulift.{v} V) _ $
  add_equiv.to_add_monoid_hom add_equiv.ulift

end semi_normed_group

namespace SemiNormedGroup

def ulift : SemiNormedGroup.{u} ⥤ SemiNormedGroup.{max u v} :=
{ obj := λ V, of (ulift.{v} V),
  map := λ V W f,
  { to_fun := λ v, ⟨f v.down⟩,
    map_add' := by { rintros ⟨x⟩ ⟨y⟩, congr, apply f.map_add, },
    bound' := by { obtain ⟨C, h1, h2⟩ := f.bound, refine ⟨C, _⟩, rintro ⟨x⟩, apply h2, } },
  map_id' := λ V, by { ext, refl },
  map_comp' := by { intros, ext, refl } }

open_locale nnreal

noncomputable
instance ulift.normed_with_aut (r : ℝ≥0) (V : SemiNormedGroup.{u}) [normed_with_aut r V] :
  normed_with_aut r (SemiNormedGroup.ulift.{v u}.obj V) :=
{ T :=  ulift.map_iso normed_with_aut.T,
  norm_T := λ v, normed_with_aut.norm_T _ }

end SemiNormedGroup
