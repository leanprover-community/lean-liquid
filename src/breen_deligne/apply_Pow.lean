import breen_deligne.eval1half
import for_mathlib.nat_iso_map_homological_complex

noncomputable theory

universes v

namespace category_theory
namespace preadditive
open category_theory category_theory.limits

variables {C D : Type*} [category.{v} C] [category.{v} D] [preadditive C] [preadditive D]
  [has_finite_biproducts C] [has_finite_biproducts D] (F : C ⥤ D) [functor.additive F]
  (F' : C ⥤ D) [functor.additive F'] (τ : F ⟶ F') (n : ℕ)

@[simps]
def apply_Pow : Pow n ⋙ F ≅ F ⋙ Pow n := nat_iso.of_components (λ A,
  { hom := biproduct.lift (λ i, F.map (biproduct.π _ i)),
    inv := biproduct.desc (λ i, F.map (biproduct.ι _ i)),
    hom_inv_id' := by simpa only [biproduct.lift_desc, ← F.map_comp, ← F.map_sum,
      biproduct.total] using F.map_id _,
    inv_hom_id' := begin
      ext i j,
      by_cases i = j,
      { subst h,
        dsimp,
        simp only [biproduct.ι_desc_assoc, category.assoc, biproduct.lift_π,
          category.comp_id, biproduct.ι_π_self, ← F.map_comp, F.map_id], },
      { dsimp,
        simp only [biproduct.ι_desc_assoc, category.assoc, biproduct.lift_π,
          category.comp_id, ← F.map_comp, limits.biproduct.ι_π_ne _ h,
          functor.map_zero], },
    end, })
(λ X Y f, by { ext, simp only [category.assoc, biproduct.lift_π,
  functor.comp_map, Pow_map, biproduct.lift_map, ← F.map_comp, biproduct.map_π], })

lemma apply_Pow_naturality (M : C) :
  τ.app ((Pow n).obj M) ≫ (apply_Pow F' n).hom.app M =
  (apply_Pow F n).hom.app M ≫ (Pow n).map (τ.app M) :=
begin
  rw [← cancel_epi ((apply_Pow F n).inv.app M)],
  slice_rhs 1 2 { rw [← nat_trans.comp_app, iso.inv_hom_id], },
  erw category.id_comp,
  apply limits.biproduct.hom_ext,
  intro j,
  apply limits.biproduct.hom_ext',
  intro i,
  simp only [apply_Pow_inv_app, apply_Pow_hom_app, category.assoc,
    biproduct.lift_π, biproduct.ι_desc_assoc, Pow_map, biproduct.map_π],
  erw [τ.naturality_assoc, ← F'.map_comp],
  by_cases i = j,
  { subst h,
    erw [biproduct.ι_π_self_assoc, biproduct.ι_π_self, F'.map_id, category.comp_id], },
  { erw [biproduct.ι_π_ne_assoc _ h, biproduct.ι_π_ne _ h, F'.map_zero, comp_zero, zero_comp], },
end

open breen_deligne breen_deligne.universal_map

variables {A₁ A₂ : Type*} [category.{v} A₁] [category.{v} A₂] [preadditive A₁] [preadditive A₂]
  [has_finite_biproducts A₁] [has_finite_biproducts A₂]
  (F₁ : A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂) (G : A₁ ⥤ A₂)
  [functor.additive G]

def eval_Pow_functor_comp (e : F₁ ⋙ G ≅ G ⋙ F₂) :
  eval_Pow_functor F₂ ⋙ ((whiskering_left _ _ A₂).obj G) ≅
  eval_Pow_functor F₁ ⋙ (whiskering_right A₁ _ _).obj G :=
nat_iso.of_components
(λ n, begin
  apply iso.symm,
  refine (functor.associator _ _ _) ≪≫ iso_whisker_left _ e ≪≫ _,
  refine (functor.associator _ _ _).symm ≪≫ _ ≪≫ (functor.associator _ _ _),
  refine iso_whisker_right (apply_Pow G n) _,
end)
(λ n m f, begin
  ext M,
  dsimp only [whiskering_right, whiskering_left, functor.associator, iso.symm,
    iso_whisker_left, iso_whisker_right, iso.trans, nat_trans.comp_app,
    functor.map_iso, eval_Pow_functor, functor.comp_map, whisker_right, whisker_left],
  repeat { erw category.id_comp, },
  repeat { erw category.comp_id, },
  rw [map_eval_Pow f F₁ G M, category.assoc, ← congr_eval_Pow' f e.inv],
  simp only [← category.assoc],
  congr' 1,
  revert f,
  let φ₁ : universal_map n m →+ ((G ⋙ Pow n ⋙ F₂).obj M ⟶ F₂.obj ((Pow m ⋙ G).obj M)) :=
  { to_fun := λ f, ((eval_Pow F₂) f).app (G.obj M) ≫ F₂.map ((apply_Pow G m).inv.app M),
    map_zero' := by simp only [eval_Pow_zero, nat_trans.app_zero, zero_comp],
    map_add' := λ f₁ f₂, by simp only [map_add, nat_trans.app_add, add_comp], },
  let φ₂ : universal_map n m →+ ((G ⋙ Pow n ⋙ F₂).obj M ⟶ F₂.obj ((Pow m ⋙ G).obj M)) :=
  { to_fun := λ f, F₂.map ((apply_Pow G n).inv.app M) ≫ ((eval_Pow' (G ⋙ F₂)) f).app M,
    map_zero' := by simp only [map_zero, nat_trans.app_zero, comp_zero],
    map_add' := λ f₁ f₂, by simp only [map_add, nat_trans.app_add, comp_add], },
  suffices : φ₁ = φ₂,
  { intro f,
    change φ₁ f = φ₂ f,
    rw this, },
  ext f,
  dsimp only [φ₁, φ₂], clear φ₁ φ₂,
  simp only [add_monoid_hom.coe_mk, eval_Pow'_of, eval_Pow_of, whisker_right_app,
    ← F₂.map_comp, functor.comp_map],
  congr' 1,
  erw [← cancel_mono ((apply_Pow G m).hom.app M), category.assoc,
    ← nat_trans.comp_app, iso.inv_hom_id, nat_trans.id_app, category.comp_id],
  simp only [basic_universal_map.eval_Pow_app, apply_Pow_inv_app,
    apply_Pow_hom_app, category.assoc],
  apply limits.biproduct.hom_ext,
  intro j,
  apply limits.biproduct.hom_ext',
  intro i,
  simp only [biproduct.matrix_π, biproduct.ι_desc, category.assoc, biproduct.lift_π,
    biproduct.ι_desc_assoc, ← G.map_comp, G.map_zsmul, G.map_id],
end)

end preadditive

end category_theory

namespace breen_deligne

namespace data

open category_theory category_theory.limits category_theory.preadditive
open universal_map

variables  {A₁ A₂ : Type*} [category.{v} A₁] [category.{v} A₂]
  [preadditive A₁] [preadditive A₂] [has_finite_biproducts A₁] [has_finite_biproducts A₂]
  (BD : data)
  (F₁ : A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂) (G : A₁ ⥤ A₂) [functor.additive G]
  (e : F₁ ⋙ G ≅ G ⋙ F₂)

instance additive_whiskering_left :
  functor.additive ((whiskering_left _ _ A₂).obj G) := { }
instance additive_whiskering_right :
  functor.additive ((whiskering_right A₁ _ _).obj G) := { }

include e
def eval_functor'_comp :
  (eval_functor' F₂ ⋙ ((whiskering_left _ _ A₂).obj G).map_homological_complex _ ≅
  eval_functor' F₁ ⋙ ((whiskering_right A₁ _ _).obj G).map_homological_complex _) :=
category_theory.nat_iso.map_homological_complex (eval_Pow_functor_comp F₁ F₂ G e) _

def eval_functor_comp :
  eval_functor F₂ ⋙ (whiskering_left _ _ _).obj G ≅
  eval_functor F₁ ⋙ (whiskering_right A₁ _ _).obj (G.map_homological_complex _) :=
iso_whisker_right (eval_functor'_comp F₁ F₂ G e) homological_complex.functor_eval.flip

end data

end breen_deligne
