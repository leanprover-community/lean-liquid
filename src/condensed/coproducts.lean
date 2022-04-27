import condensed.is_proetale_sheaf
import condensed.top_comparison
import condensed.adjunctions

/-!
We show that passing from a profinite set to a condensed set
preserves (finite) coproducts.
-/

open_locale big_operators classical
open category_theory
open category_theory.limits
open opposite

universe u

namespace Profinite

@[simps]
def to_Condensed_equiv (X : Profinite.{u}) (Y : CondensedSet.{u}) :
  (X.to_Condensed ⟶ Y) ≃ Y.val.obj (op X) :=
{ to_fun := λ f, f.val.app _ $ ulift.up $ 𝟙 _,
  inv_fun := λ f, Sheaf.hom.mk $
  { app := λ T g, Y.val.map (quiver.hom.op (ulift.down g)) f,
    naturality' := sorry },
  left_inv := sorry,
  right_inv := sorry }

end Profinite

namespace CondensedSet

variables {α : Type u} [fintype α] (X : α → Profinite.{u})

@[simps]
def sigma_cone : cocone (discrete.functor X ⋙ Profinite_to_Condensed) :=
{ X := (Profinite.sigma X).to_Condensed,
  ι :=
  { app := λ i, Profinite_to_Condensed.map $ Profinite.sigma.ι X i,
    naturality' := begin
      rintros i j ⟨⟨⟨⟩⟩⟩, dsimp, simp, dsimp, simp, dsimp, simp,
    end } } .

noncomputable
def val_obj_sigma_equiv (Y : CondensedSet.{u}) :
  Y.val.obj (op $ Profinite.sigma X) ≃ (Π (a : α), Y.val.obj (op $ X a)) :=
equiv.of_bijective
(λ f a, Y.val.map (Profinite.sigma.ι X a).op f)
begin
  have := Y.2,
  rw is_sheaf_iff_is_sheaf_of_type at this,
  rw Y.val.is_proetale_sheaf_of_types_tfae.out 0 4 at this,
  have key := this.1,
  exact key ⟨α⟩ X,
end

noncomputable
def _root_.Condensed.val_obj_sigma_add_equiv
  (Y : Condensed.{u} Ab.{u+1}) :
  Y.val.obj (op $ Profinite.sigma X) ≃+
  (Π (a : α), Y.val.obj (op $ X a)) :=
add_equiv.of_bijective
{ to_fun := λ f a, Y.val.map (Profinite.sigma.ι X a).op f,
  map_zero' := by { ext1, simp },
  map_add' := λ x y, by { ext1, simp } }
((Condensed_Ab_to_CondensedSet.obj Y).val_obj_sigma_equiv X).bijective

@[simp]
lemma coe_val_obj_sigma_equiv (Y : Condensed.{u} Ab.{u+1}) :
  ⇑((Condensed_Ab_to_CondensedSet.obj Y).val_obj_sigma_equiv X) =
  (Y.val_obj_sigma_add_equiv X) := rfl

@[simp]
lemma coe_val_obj_sigma_equiv_symm (Y : Condensed.{u} Ab.{u+1}) :
  ⇑((Condensed_Ab_to_CondensedSet.obj Y).val_obj_sigma_equiv X).symm =
  (Y.val_obj_sigma_add_equiv X).symm := rfl

@[simp]
lemma _root_.Condensed.val_obj_sigma_add_equiv_apply_apply
  (Y : Condensed.{u} Ab.{u+1}) (t) (a) :
  Y.val_obj_sigma_add_equiv X t a = Y.val.map (Profinite.sigma.ι X a).op t := rfl

noncomputable
def is_colimit_sigma_cone : is_colimit (sigma_cone X) :=
{ desc := λ S, (Profinite.to_Condensed_equiv _ _).symm $
    (S.X.val_obj_sigma_equiv X).symm $ λ a,
    (Profinite.to_Condensed_equiv _ _) $ S.ι.app _,
  fac' := sorry,
  uniq' := sorry }

end CondensedSet
