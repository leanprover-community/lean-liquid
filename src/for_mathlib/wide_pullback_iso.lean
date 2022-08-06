import category_theory.limits.shapes.wide_pullbacks
import category_theory.limits.preserves.limits
import category_theory.limits.yoneda
import category_theory.limits.types

namespace category_theory

open category_theory.limits

universes u
variables {C : Type (u+1)} [category.{u} C] [has_wide_pullbacks.{0} C]

set_option pp.universes true

open opposite

noncomputable theory
def ulift_wide_pullback_iso_hom_aux (i : ℕ) (T B X : C)
  (f : X ⟶ B) :
ulift_functor.{u+1}.obj (T ⟶ wide_pullback B (λ _ : fin i, X) (λ _, f)) ⟶
wide_pullback
  (ulift.{u+1 u} $ T ⟶ B)
  (λ _ : fin i, ulift.{u+1 u} $ T ⟶ X)
  (λ _, ulift_functor.map $ (yoneda.map f).app (opposite.op T)) :=
wide_pullback.lift
(ulift_functor.map $ (yoneda.map $ wide_pullback.base _).app (opposite.op T))
(λ q, ulift_functor.map $ (yoneda.map $ wide_pullback.π _ $ q).app (opposite.op T))
begin
  rintros ⟨j⟩,
  rw ← functor.map_comp,
  congr' 1,
  ext q,
  dsimp [yoneda],
  rw ← wide_pullback.π_arrow,
  rw category.assoc,
end

def ulift_wide_pullback_iso_inv_aux (i : ℕ) (T B X : C) (f : X ⟶ B) :
wide_pullback
  (ulift.{u+1 u} $ T ⟶ B)
  (λ _ : fin i, ulift.{u+1 u} $ T ⟶ X)
  (λ _, ulift_functor.map $ (yoneda.map f).app (opposite.op T)) ⟶
  ulift_functor.{u+1}.obj (T ⟶ wide_pullback B (λ _ : fin i, X) (λ _, f)) :=
let b : wide_pullback
  (ulift.{u+1 u} $ T ⟶ B)
  (λ _ : fin i, ulift.{u+1 u} $ T ⟶ X)
  (λ _, ulift_functor.map $ (yoneda.map f).app (opposite.op T)) ⟶ _ :=
  wide_pullback.base _,
  π : Π (q : fin i), wide_pullback
  (ulift.{u+1 u} $ T ⟶ B)
  (λ _ : fin i, ulift.{u+1 u} $ T ⟶ X)
  (λ _, ulift_functor.map $ (yoneda.map f).app (opposite.op T)) ⟶ _  :=
  wide_pullback.π _ in
λ t, ulift.up $
wide_pullback.lift
(b t).down
(λ q : fin i, (π q t).down)
begin
  rintros ⟨j⟩,
  dsimp [b, π], rw ← wide_pullback.π_arrow, refl,
end

def ulift_wide_pullback_iso (i : ℕ) (T B X : C) (f : X ⟶ B) :
ulift_functor.{u+1}.obj (T ⟶ wide_pullback B (λ _ : fin i, X) (λ _, f)) ≅
wide_pullback
  (ulift.{u+1 u} $ T ⟶ B)
  (λ _ : fin i, ulift.{u+1 u} $ T ⟶ X)
  (λ _, ulift_functor.map $ (yoneda.map f).app (opposite.op T)) :=
{ hom := ulift_wide_pullback_iso_hom_aux _ _ _ _ _,
  inv := ulift_wide_pullback_iso_inv_aux _ _ _ _ _,
  hom_inv_id' := begin
    dsimp [
      ulift_wide_pullback_iso_hom_aux,
      ulift_wide_pullback_iso_inv_aux],
    ext t : 2, dsimp, apply wide_pullback.hom_ext, rintros ⟨j⟩,
    { simp only [wide_pullback.lift_π],
      have := types_comp_apply
        (wide_pullback.lift (ulift_functor.{u+1 u}.map
          ((yoneda.{u u+1}.map (wide_pullback.base (λ (_x : fin i), f))).app (op.{u+2} T)))
          (λ (q : fin i), ulift_functor.{u+1 u}.map
          ((yoneda.{u u+1}.map (wide_pullback.π (λ (_x : fin i), f) q)).app (op.{u+2} T))) _)
        (wide_pullback.π (λ (_x : fin i), ulift_functor.{u+1 u}.map
          ((yoneda.{u u+1}.map f).app (op.{u+2} T))) _) t,
      rw [← this, wide_pullback.lift_π], refl },
    { simp only [wide_pullback.lift_base],
      have := types_comp_apply
        (wide_pullback.lift (ulift_functor.{u+1 u}.map
          ((yoneda.{u u+1}.map (wide_pullback.base (λ (_x : fin i), f))).app (op.{u+2} T)))
          (λ (q : fin i), ulift_functor.{u+1 u}.map
          ((yoneda.{u u+1}.map (wide_pullback.π (λ (_x : fin i), f) q)).app (op.{u+2} T))) _)
        (wide_pullback.base (λ (_x : fin i),
          ulift_functor.{u+1 u}.map ((yoneda.{u u+1}.map f).app (op.{u+2} T)))) t,
      rw [← this, limits.wide_pullback.lift_base], refl }
  end,
  inv_hom_id' := begin
    dsimp [
      ulift_wide_pullback_iso_hom_aux,
      ulift_wide_pullback_iso_inv_aux],
    ext ⟨t⟩ : 1,
    { simp only [category.assoc, wide_pullback.lift_π, category.id_comp],
      ext x, dsimp, simp, },
    { simp only [category.assoc, wide_pullback.lift_base, category.id_comp],
      ext x, dsimp, simp }
  end }

end category_theory
