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
    naturality' := begin
      intros A B ff, ext t,
      obtain ⟨t⟩ := t,
      dsimp [Profinite.to_Condensed, ulift_functor, yoneda] at ⊢ t,
      simp only [functor.map_comp], refl,
    end },
  left_inv := λ f, begin
    ext T ⟨t⟩,
    dsimp [yoneda] at ⊢ t,
    change (f.val.app _ ≫ Y.val.map _) _ = _,
    rw ← nat_trans.naturality,
    change f.val.app _ _ = _,
    congr' 1, ext, refl,
  end,
  right_inv := λ f, by { dsimp, simp } }

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
(add_monoid_hom.mk' (λ f a, Y.val.map (Profinite.sigma.ι X a).op f) (by { intros, ext1, simp }))
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

lemma val_obj_sigma_equiv_symm_apply'
  (Y : CondensedSet.{u})
  (e : Π (a : α), Y.val.obj (op $ X a)) (a₀ : α) :
  (Y.val.map (Profinite.sigma.ι X a₀).op)
  (((val_obj_sigma_equiv X Y).symm) e) = e a₀ :=
begin
  let e' := _, change (Y.val.map (Profinite.sigma.ι X a₀).op) e' = _,
  have : e a₀ = (val_obj_sigma_equiv X Y) e' a₀,
    { revert a₀, rw ← function.funext_iff, dsimp only [e'], simp },
  rw this, refl,
end

-- TODO reuse the nonadditive variant for this.
lemma _root_.Condensed.val_obj_sigma_add_equiv_symm_apply'
  (Y : Condensed.{u} Ab.{u+1})
  (e : Π (a : α), Y.val.obj (op $ X a)) (a₀ : α) :
  (Y.val.map (Profinite.sigma.ι X a₀).op)
  (((_root_.Condensed.val_obj_sigma_add_equiv X Y).symm) e) = e a₀ :=
begin
  let e' := _, change (Y.val.map (Profinite.sigma.ι X a₀).op) e' = _,
  have : e a₀ = (_root_.Condensed.val_obj_sigma_add_equiv X Y) e' a₀,
    { revert a₀, rw ← function.funext_iff, dsimp only [e'], simp },
  rw this, refl,
end

lemma val_obj_sigma_equiv_symm_apply
  (Y : CondensedSet.{u})
  (e : Π (a : α), Y.val.obj (op $ X a)) (a₀ : α) :
    (Profinite_to_Condensed.map (Profinite.sigma.ι X a₀)) ≫
    (Profinite.to_Condensed_equiv (Profinite.sigma X) Y).symm
    ((Y.val_obj_sigma_equiv X).symm e) =
    (Profinite.to_Condensed_equiv (X a₀) Y).symm (e a₀) :=
begin
  apply_fun ((X a₀).to_Condensed_equiv Y),
  simp only [equiv.apply_symm_apply],
  dsimp [Profinite.to_Condensed_equiv],
  simp only [category.comp_id],
  apply val_obj_sigma_equiv_symm_apply'
end

-- TODO reuse the nonadditive variant for this.
lemma _root_.Condensed.val_obj_sigma_add_equiv_symm_apply
  (Y : Condensed.{u} Ab.{u+1})
  (e : Π (a : α), Y.val.obj (op $ X a)) (a₀ : α) :
    (Profinite_to_Condensed.map (Profinite.sigma.ι X a₀)) ≫
    (Profinite.to_Condensed_equiv (Profinite.sigma X)
    (Condensed_Ab_to_CondensedSet.obj Y)).symm
    ((Y.val_obj_sigma_add_equiv X).symm e) =
    (Profinite.to_Condensed_equiv (X a₀)
    (Condensed_Ab_to_CondensedSet.obj Y)).symm (e a₀) :=
begin
  apply_fun ((X a₀).to_Condensed_equiv (Condensed_Ab_to_CondensedSet.obj Y)),
  simp only [equiv.apply_symm_apply],
  dsimp [Profinite.to_Condensed_equiv],
  simp only [category.comp_id],
  apply _root_.Condensed.val_obj_sigma_add_equiv_symm_apply'
end

noncomputable
def is_colimit_sigma_cone : is_colimit (sigma_cone X) :=
{ desc := λ S, (Profinite.to_Condensed_equiv _ _).symm $
    (S.X.val_obj_sigma_equiv X).symm $ λ a,
    (Profinite.to_Condensed_equiv _ _) $ S.ι.app _,
  fac' := begin
    intros Q T,
    dsimp,
    rw val_obj_sigma_equiv_symm_apply,
    ext W ⟨(t : _ ⟶ _)⟩,
    dsimp [Profinite.to_Condensed_equiv],
    change ((Q.ι.app T).val.app (op (X T)) ≫ Q.X.val.map t.op) _ = _,
    erw ← (Q.ι.app T).val.naturality,
    change (Q.ι.app T).val.app (op (unop W)) _ = _,
    congr' 1,
    dsimp [Profinite.to_Condensed], ext, refl,
  end,
  uniq' := begin
    intros S m hm,
    apply_fun ((Profinite.sigma X).to_Condensed_equiv S.X),
    apply_fun (val_obj_sigma_equiv X S.X),
    simp only [equiv.apply_symm_apply],
    ext a,
    specialize hm a,
    dsimp [val_obj_sigma_equiv],
    change (m.val.app (op (Profinite.sigma X)) ≫
      S.X.val.map _) _ = _,
    rw ← m.val.naturality,
    apply_fun (λ e, e.val.app (op (X a)) ⟨𝟙 _⟩) at hm,
    exact hm,
  end }

end CondensedSet
