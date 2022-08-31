import condensed.tensor
import for_mathlib.preserves_finite_limits

noncomputable theory

universes u
open_locale tensor_product

open category_theory category_theory.limits opposite

namespace AddCommGroup

@[reassoc]
lemma map_tensor_flip {A B C D : AddCommGroup} (f : A ⟶ B) (g : C ⟶ D) :
  map_tensor f g ≫ (tensor_flip _ _).hom = (tensor_flip _ _).hom ≫ map_tensor g f :=
by { apply AddCommGroup.tensor_ext, intros a c, refl }

end AddCommGroup

namespace Condensed

def tensor_tunit (A : AddCommGroup) (h : AddCommGroup.is_tensor_unit A) :
  tensor_functor.flip.obj A ≅ 𝟭 _ :=
begin
  refine _ ≪≫ (Condensed_ExtrSheaf_equiv Ab).counit_iso,
  refine nat_iso.of_components _ _,
  { intro M,
    refine (Condensed_ExtrSheaf_equiv Ab).functor.map_iso _,
    refine Sheaf.iso.mk _ _ _,
    refine nat_iso.of_components _ _,
    { intro S,
      refine (AddCommGroup.tensor_functor_iso_flip.app _).app _ ≪≫ _,
      refine AddCommGroup.tensor_unit_iso _ _ h, },
    { intros S T f,
      dsimp [ExtrSheaf.tensor, AddCommGroup.tensor_functor_iso_flip],
      simp only [category.assoc],
      erw AddCommGroup.tensor_unit_iso_naturality,
      rw ← AddCommGroup.map_tensor_flip_assoc, refl, } },
  { intros M N f,
    dsimp only [tensor_functor, map_tensor, functor.flip_obj_map,
      functor.comp_map, functor.map_iso_hom],
    simp only [← functor.map_comp], congr' 1,
    ext S : 3,
    dsimp only [Sheaf.category_theory.category_comp_val, ExtrSheaf.map_tensor_val, Sheaf.iso.mk_hom_val,
      nat_iso.of_components_hom_app, nat_trans.comp_app,
      ExtrSheafProd.map_tensor_val_app, iso.trans_hom],
    simp only [category.assoc],
    dsimp [AddCommGroup.tensor_functor_iso_flip],
    rw [AddCommGroup.map_tensor_flip_assoc], congr' 1,
    symmetry, apply AddCommGroup.tensor_unit_iso_naturality, }
end

def tensor_punit :
  tensor_functor.flip.obj (AddCommGroup.of (punit →₀ ℤ)) ≅ 𝟭 _ :=
tensor_tunit _ $
begin
  dsimp [AddCommGroup.is_tensor_unit],
  refine ⟨finsupp.single punit.star 1, _⟩,
  intro B, split,
  { intros f g h, ext ⟨⟩, exact h },
  { intros b, refine ⟨(finsupp.total _ _ _ _).to_add_monoid_hom, _⟩,
    { intro, exact b },
    { dsimp, simp only [finsupp.total_single, one_zsmul], } }
end

-- See comment around L20
instance preserves_mono_tensor_functor (A : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))]
  {X Y : Ab} (f : X ⟶ Y) [mono f] :
  mono ((tensor_functor.obj A).map f) :=
begin
  suffices : mono (ExtrSheaf.map_tensor ((Condensed_ExtrSheaf_equiv Ab).inverse.map (𝟙 A)) f),
  { dsimp only [tensor_functor, map_tensor], resetI, apply_instance },
  constructor, intros X φ ψ h, ext S : 3,
  apply_fun (λ η, η.val.app S) at h,
  dsimp [ExtrSheaf.map_tensor] at h,
  refine (@cancel_mono _ _ _ _ _ _ (id _) _ _).mp h,
  apply_with AddCommGroup.tensor_obj_map_preserves_mono {instances:=ff},
  apply_instance, apply_assumption
end
.



/-
We need one of the following two sorries.
If we prove the first, we can deduce the second using `exact_functor.lean`
But maybe it is easier to just prove `preserves_finite_limits_tensor_functor` second directly.
-/

-- lemma tensor_eval_iso_natural_right
--   (A : (Condensed.{u} Ab.{u+1})) {X Y : Ab} (f : X ⟶ Y) (S : ExtrDisc) :
--   AddCommGroup.map_tensor (𝟙 (A.val.obj (op S.val))) f ≫ (tensor_eval_iso A Y S).inv =
--   (tensor_eval_iso A X S).inv ≫ ((tensor_functor.obj A).map f).val.app (op S.val) :=
-- begin
--   rw [iso.comp_inv_eq],
--   dsimp only [tensor_eval_iso, tensor_functor, map_tensor,
--     functor.map_iso_hom, iso.app_hom, functor.map_iso_inv, iso.app_inv, iso.symm_hom, iso.symm_inv,
--     Sheaf_to_presheaf_map],
--   -- erw [equivalence.unit_app_inverse],
--   admit
-- end

-- lemma tensor_short_exact (A : (Condensed.{u} Ab.{u+1}))
--   [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))]
--   {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g) :
--   short_exact ((tensor_functor.obj A).map f) ((tensor_functor.obj A).map g) :=
-- begin
--   rw short_exact_iff_ExtrDisc, intro S,
--   let eX := tensor_eval_iso A X S,
--   let eY := tensor_eval_iso A Y S,
--   let eZ := tensor_eval_iso A Z S,
--   refine commsq.short_exact.of_iso eX.inv eY.inv eZ.inv _ _ _,
--   { refine (AddCommGroup.tensor_functor.obj _).map f, },
--   { refine (AddCommGroup.tensor_functor.obj _).map g, },
--   { apply AddCommGroup.tensor_short_exact, exact hfg },
--   { apply commsq.of_eq, apply tensor_eval_iso_natural_right },
--   { apply commsq.of_eq, apply tensor_eval_iso_natural_right },
-- end

-- See comment around L20
instance preserves_finite_limits_tensor_functor (A : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))] :
  preserves_finite_limits (tensor_functor.obj A) :=
preserves_finite_limits_of_preserves_mono_preserves_finite_colimits _ $
λ X Y f hf, by { resetI, apply_instance }

end Condensed
