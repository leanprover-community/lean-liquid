import category_theory.limits.concrete_category
import for_mathlib.sheafification.plus_sheaf_condition

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w v u
variables {C : Type u} [category.{v} C] {D : Type w}
  [category.{max v u} D] (J : grothendieck_topology C)

variables [has_limits D] [has_colimits D]
variables [concrete_category.{max v u} D]
variables [preserves_limits (forget D)]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

local attribute [instance]
  concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

theorem injective_to_plus_app (P : Cᵒᵖ ⥤ D) (X : C) :
  function.injective ((J.to_plus_app P).app (op X)) := sorry

theorem plus_ext  (P : Cᵒᵖ ⥤ D)
  (X : C) (S : J.cover X) (x y : (plus_obj J P).obj (op X))
  (h : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f),
    (plus_obj J P).map f.op x = (plus_obj J P).map f.op y) : x = y :=
begin
  dsimp at x,
  obtain ⟨jx,x,rfl⟩ := concrete.is_colimit_exists_rep (J.diagram P X)
    (colimit.is_colimit _) x,
  obtain ⟨jy,y,rfl⟩ := concrete.is_colimit_exists_rep (J.diagram P X)
    (colimit.is_colimit _) y,
  let z := jx.unop ⊓ jy.unop ⊓ S,
  let ex : jx ⟶ op z := eq_to_hom (by simp) ≫
    (hom_of_le (le_trans inf_le_left inf_le_left)).op,
  let ey : jy ⟶ op z := eq_to_hom (by simp) ≫
    (hom_of_le (le_trans inf_le_left inf_le_right)).op,
  let eS : op S ⟶ op z := (hom_of_le inf_le_right).op,
  dsimp,
  rw [← colimit.w _ ex, ← colimit.w _ ey],
  --have := concrete.to_product_injective_of_is_limit,
  dsimp only [plus_obj] at h,
  simp_rw [← comp_apply] at h,
  dsimp at h,
  simp only [colimit.ι_pre, ι_colim_map_assoc] at h,
  simp_rw [comp_apply],
  congr' 1,
  apply concrete.to_product_injective_of_is_limit _ (limit.is_limit _),
  swap, apply_instance,
  dsimp,
  simp,
  -- I need a condition in a concrete category saying when two members of a colimit
  -- are equal.
  ext1 (a|b),
  { dsimp [multifork.of_ι],
    specialize h a.f _,
    { apply le_of_hom eS.unop,
      exact a.hf },
    sorry,
  },
  { sorry }
end

theorem is_sheaf_of_ext
  (P : Cᵒᵖ ⥤ D) (h : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X))
    (hh : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), P.map f.op x = P.map f.op y), x = y) :
  presheaf.is_sheaf J (J.plus_obj P) :=
begin
  rw presheaf.is_sheaf_iff_multiequalizer,
  intros X S,
  suffices : is_iso ((forget D).map $ S.to_multiequalizer (J.plus_obj P)),
  { apply is_iso_of_reflects_iso _ (forget D), exact this, },
  rw is_iso_iff_bijective,
  dsimp,
  split,
  { sorry },
  { sorry }
end

end category_theory.grothendieck_topology
