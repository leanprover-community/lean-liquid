import condensed.tensor
import for_mathlib.AddCommGroup.tensor_short_exact

noncomputable theory

universes u
open_locale tensor_product

open category_theory category_theory.limits opposite

namespace Condensed

def tensor_punit :
  tensor_functor.flip.obj (AddCommGroup.of (punit →₀ ℤ)) ≅ 𝟭 _ :=
sorry


/-
We need one of the following two sorries.
If we prove the first, we can deduce the second using `exact_functor.lean`
But maybe it is easier to just prove `preserves_finite_limits_tensor_functor` second directly.
-/

lemma tensor_eval_iso_natural_right
  (A : (Condensed.{u} Ab.{u+1})) {X Y : Ab} (f : X ⟶ Y) (S : ExtrDisc) :
  AddCommGroup.map_tensor (𝟙 (A.val.obj (op S.val))) f ≫ (tensor_eval_iso A Y S).inv =
  (tensor_eval_iso A X S).inv ≫ ((tensor_functor.obj A).map f).val.app (op S.val) :=
begin
  rw [iso.comp_inv_eq],
  dsimp only [tensor_eval_iso, tensor_functor, map_tensor,
    functor.map_iso_hom, iso.app_hom, functor.map_iso_inv, iso.app_inv, iso.symm_hom, iso.symm_inv,
    Sheaf_to_presheaf_map, tensor_iso],
  -- erw [equivalence.unit_app_inverse],
  sorry
end

lemma tensor_short_exact (A : (Condensed.{u} Ab.{u+1}))
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))]
  {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g) :
  short_exact ((tensor_functor.obj A).map f) ((tensor_functor.obj A).map g) :=
begin
  rw short_exact_iff_ExtrDisc, intro S,
  let eX := tensor_eval_iso A X S,
  let eY := tensor_eval_iso A Y S,
  let eZ := tensor_eval_iso A Z S,
  refine commsq.short_exact.of_iso eX.inv eY.inv eZ.inv _ _ _,
  { refine (AddCommGroup.tensor_functor.obj _).map f, },
  { refine (AddCommGroup.tensor_functor.obj _).map g, },
  { apply AddCommGroup.tensor_short_exact, exact hfg },
  { apply commsq.of_eq, apply tensor_eval_iso_natural_right },
  { apply commsq.of_eq, apply tensor_eval_iso_natural_right },
end

-- See comment around L20
instance preserves_finite_limits_tensor_functor (A : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))] :
  preserves_finite_limits (tensor_functor.obj A) :=
sorry

end Condensed
