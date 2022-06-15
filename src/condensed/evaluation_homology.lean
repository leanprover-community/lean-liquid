import condensed.top_comparison
import condensed.exact
import for_mathlib.exact_functor

.

open category_theory
open category_theory.limits
open opposite

namespace Condensed

universes u

variables {X Y Z : Condensed.{u} Ab.{u+1}} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
  (S : Profinite.{u})

noncomputable theory

instance evaluation_additive (S : Profinite.{u}) :
  functor.additive (Condensed.evaluation _ S : Condensed.{u} Ab.{u+1} ⥤ _) :=
⟨λ X Y f g, rfl⟩

lemma evaluation_exact (S : ExtrDisc.{u}) :
  functor.exact (Condensed.evaluation _ S.val : Condensed.{u} Ab.{u+1} ⥤ _) :=
begin
  intros X Y Z f g h,
  rw Condensed.exact_iff_ExtrDisc at h,
  apply h
end

abbreviation homology_evaluation_iso (S : ExtrDisc.{u}) :
  (homology f g w).val.obj (op S.val) ≅
  homology (f.val.app (op S.val)) (g.val.app (op S.val))
    (by { rw [← f.val.comp_app, ← Sheaf.hom.comp_val, w], refl }) :=
(Condensed.evaluation Ab.{u+1} _).homology_iso _ _ _ _

.

abbreviation homology_functor_evaluation_iso {M : Type*} (c : complex_shape M)
  (i : M) (S : ExtrDisc.{u}) :
  homology_functor (Condensed.{u} Ab.{u+1}) c i ⋙ Condensed.evaluation _ S.val ≅
  (Condensed.evaluation _ S.val).map_homological_complex _ ⋙ homology_functor Ab.{u+1} c i :=
(Condensed.evaluation Ab.{u+1} _).homology_functor_iso _ _

end Condensed
