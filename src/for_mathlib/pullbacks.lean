import tactic
import category_theory.limits.shapes.pullbacks

namespace category_theory
open category_theory.limits

variables {C D : Type*} [category C] [category D] (e : C ≌ D)
  {X Y B : D} (f : X ⟶ B) (g : Y ⟶ B) [has_pullback (e.inverse.map f) (e.inverse.map g)]

lemma equivalence.hom_eq_map {X Y : C} (f : e.functor.obj X ⟶ e.functor.obj Y)
  (g : X ⟶ Y) : e.inverse.map f = e.symm.counit.app _ ≫ g ≫ e.unit.app _ →
  f = e.functor.map g :=
begin
  intros h,
  change _ = (e.unit_iso.app _).inv ≫ g ≫ (e.unit_iso.app _).hom at h,
  rw iso.eq_inv_comp at h,
  replace h := h.symm,
  rw ← iso.eq_comp_inv at h,
  rw h,
  simp,
  nth_rewrite 0 ← category.id_comp f,
  simp_rw ← category.assoc,
  congr' 1,
  simp,
end


noncomputable theory

/-
I would like to do something for more general shapes, but universes make this difficult
(as usual...)
-/

@[simps]
def equivalence.pullback_cone : cone (cospan f g) :=
{ X := e.functor.obj $ pullback (e.inverse.map f) (e.inverse.map g),
  π :=
  { app := λ i,
    match i with
    | none := e.functor.map pullback.fst ≫ e.counit.app X ≫ f
    | walking_cospan.left := e.functor.map pullback.fst ≫ e.counit.app X
    | walking_cospan.right := e.functor.map pullback.snd ≫ e.counit.app Y
    end,
    naturality' := begin
      rintro (i|i|i) (j|j|j) (h|h),
      { dsimp, simp only [category.id_comp, functor.map_id], dsimp, simp only [category.comp_id], },
      { dsimp, simp only [category.id_comp], dsimp [equivalence.pullback_cone._match_1],
        simp only [category.assoc], },
      { dsimp, simp only [category.id_comp, functor.map_id], dsimp, simp only [category.comp_id], },
      { unfold_aux,
        dsimp, simp, delta id_rhs,
        have : e.counit.app X ≫ f = e.functor.map (e.inverse.map f) ≫ e.counit.app B, by tidy,
        rw this, clear this,
        have : e.counit.app Y ≫ g = e.functor.map (e.inverse.map g) ≫ e.counit.app B, by tidy,
        rw this, clear this,
        simp_rw [← category.assoc, ← e.functor.map_comp, limits.pullback.condition] },
      { tidy }
    end } } .

attribute [reassoc] equivalence.unit_inverse_comp

-- This is a mess :-(
-- Please fix before moving this file to mathlib!
def equivalence.is_limit_pullback_cone : limits.is_limit (e.pullback_cone f g) :=
{ lift := λ S, e.symm.unit.app S.X ≫
    e.functor.map (pullback.lift (e.inverse.map (S.π.app walking_cospan.left))
      (e.inverse.map (S.π.app walking_cospan.right)) begin
        simp_rw ← e.inverse.map_comp,
        change e.inverse.map (_ ≫ (cospan f g).map walking_cospan.hom.inl) =
          e.inverse.map (_ ≫ (cospan f g).map walking_cospan.hom.inr),
        rw [S.w, S.w],
      end),
  fac' := begin
    rintros S (j|j|j),
    { dsimp [equivalence.pullback_cone._match_1],
      simp only [category.assoc],
      have : e.counit.app X ≫ f = e.functor.map (e.inverse.map f) ≫ e.counit.app B,
      { dsimp, simp only [equivalence.fun_inv_map, category.assoc, iso.inv_hom_id_app,
          nat_iso.cancel_nat_iso_hom_left], erw category.comp_id, },
      rw this, clear this,
      simp_rw [← category.assoc _ _ (e.counit.app B), ← e.functor.map_comp],
      simp only [functor.map_comp, pullback.lift_fst_assoc, equivalence.fun_inv_map,
        category.assoc, iso.inv_hom_id_app_assoc, iso.inv_hom_id_app],
      dsimp,
      simp only [category.comp_id],
      change _ ≫ (cospan f g).map walking_cospan.hom.inl = _,
      rw S.w },
    { dsimp [equivalence.pullback_cone._match_1],
      simp only [category.assoc],
      simp_rw [← category.assoc _ _ (e.counit.app X), ← e.functor.map_comp],
      simp only [pullback.lift_fst, equivalence.fun_inv_map, iso.inv_hom_id_app_assoc,
        category.assoc, iso.inv_hom_id_app],
      dsimp,
      rw [category.comp_id] },
    { dsimp [equivalence.pullback_cone._match_1],
      simp only [category.assoc],
      simp_rw [← category.assoc _ _ (e.counit.app Y), ← e.functor.map_comp],
      simp only [pullback.lift_snd, equivalence.fun_inv_map, iso.inv_hom_id_app_assoc,
        category.assoc, iso.inv_hom_id_app],
      dsimp,
      rw [category.comp_id] }
  end,
  uniq' := begin
    intros S m h,
    --dsimp at *,
    change m = (e.counit_iso.app S.X).inv ≫ _,
    rw iso.eq_inv_comp,
    apply equivalence.hom_eq_map,
    change _ = (e.unit_iso.app _).inv ≫ _ ≫ (e.unit_iso.app _).hom,
    rw iso.eq_inv_comp,
    symmetry,
    rw ← iso.eq_comp_inv,
    simp only [category.assoc],
    apply pullback.hom_ext,
    { simp only [functor.map_comp, pullback.lift_fst, iso.app_hom, iso.app_inv, category.assoc],
      specialize h walking_cospan.left,
      rw ← h,
      simp only [functor.map_comp, equivalence.inv_fun_map, category.assoc,
        equivalence.unit_inverse_comp_assoc, category.comp_id,
        equivalence.pullback_cone, equivalence.pullback_cone_π_app, functor.map_comp,
        equivalence.unit_inverse_comp], },
    { simp only [functor.map_comp, pullback.lift_snd, iso.app_hom, iso.app_inv, category.assoc],
      specialize h walking_cospan.right,
      rw ← h,
      simp only [functor.map_comp, equivalence.inv_fun_map, category.assoc,
        equivalence.unit_inverse_comp_assoc, category.comp_id,
        equivalence.pullback_cone, equivalence.pullback_cone_π_app, functor.map_comp,
        equivalence.unit_inverse_comp], }
  end } .

include e

lemma equivalence.has_pullback {X Y B : D} (f : X ⟶ B) (g : Y ⟶ B)
  [has_pullback (e.inverse.map f) (e.inverse.map g)] : has_pullback f g :=
limits.has_limit.mk ⟨e.pullback_cone _ _, e.is_limit_pullback_cone _ _⟩

lemma equivalence.has_pullbacks [has_pullbacks C] : has_pullbacks D :=
begin
  apply has_pullbacks_of_has_limit_cospan _,
  intros X Y B f g,
  apply e.has_pullback,
end

end category_theory
