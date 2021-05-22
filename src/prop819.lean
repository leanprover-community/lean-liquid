import for_mathlib.Cech.split
import for_mathlib.Profinite.functorial_limit
import for_mathlib.simplicial.complex
import for_mathlib.SemiNormedGroup
import for_mathlib.homological_complex

import locally_constant.Vhat
import prop819.completion

open_locale nnreal

noncomputable theory

open category_theory opposite
open SemiNormedGroup

universes u

-- We have a surjective morphism of profinite sets.
variables (F : arrow Profinite.{u}) (surj : function.surjective F.hom)
variables (M : SemiNormedGroup.{u})

abbreviation FL : cochain_complex SemiNormedGroup ℕ :=
  (((cosimplicial_object.augmented.whiskering _ _).obj (LocallyConstant.{u u}.obj M)).obj
  F.augmented_cech_nerve.right_op).to_cocomplex

abbreviation FLC : cochain_complex SemiNormedGroup ℕ :=
  (((cosimplicial_object.augmented.whiskering _ _).obj (LCC.{u u}.obj M)).obj
  F.augmented_cech_nerve.right_op).to_cocomplex

--def Rop : (simplicial_object.augmented Profinite)ᵒᵖ ⥤ cosimplicial_object.augmented Profiniteᵒᵖ :=
--{ obj := λ X, X.unop.right_op,
--  map := λ X Y f,
--  { left := quiver.hom.op (comma_morphism.right f.unop),
--    right := nat_trans.right_op (comma_morphism.left f.unop),
--    w' := by { ext, exact congr_arg (λ η, (nat_trans.app η (op x)).op) f.unop.w.symm, } } }

def FLC_functor : (arrow Profinite.{u})ᵒᵖ ⥤ cochain_complex SemiNormedGroup ℕ :=
simplicial_object.augmented_cech_nerve.op ⋙
  simplicial_to_cosimplicial_augmented _ ⋙
  (cosimplicial_object.augmented.whiskering _ _).obj (LCC.{u u}.obj M) ⋙
  cosimplicial_object.augmented.cocomplex

--⊢ cosimplicial_object.δ
--      (functor.right_op F.cech_nerve ⋙ (curry.obj (uncurry.obj LocallyConstant ⋙ Completion)).obj M)
--      k =
--    Completion.map (cosimplicial_object.δ (functor.right_op F.cech_nerve ⋙ LocallyConstant.obj M) k)

lemma FLC_iso_helper {x y : simplex_category} (f : x ⟶ y) :
  (F.cech_nerve.right_op ⋙ LCC.obj M).map f =
  Completion.map ((F.cech_nerve.right_op ⋙ LocallyConstant.obj M).map f) :=
begin
  change Completion.map _ = _,
  congr' 1,
  dsimp [uncurry],
  erw locally_constant.map_hom_id,
  change 𝟙 _ ≫ _ = _,
  rw category.id_comp,
end

def FLC_iso : strict_iso ((Completion.map_homological_complex _).obj (FL F M)) (FLC F M) :=
{ iso := homological_complex.iso_of_components (λ i,
    match i with
    | 0 := eq_to_iso rfl
    | n+1 := eq_to_iso rfl
    end) begin
      rintro (_|i) (_|j) h; rcases h with _|⟨i,w⟩; ext; dsimp [FLC_iso._match_1];
        split_ifs with hh hh,
      { simp only [category.id_comp, category.comp_id, Completion_map_apply],
        dsimp only [cosimplicial_object.augmented.to_cocomplex_d,
          cosimplicial_object.augmented.drop, comma.snd, cosimplicial_object.whiskering,
          whiskering_right, cosimplicial_object.coboundary, functor.const_comp, LCC],
        simpa },
      { exfalso,
        apply hh,
        refl },
      { simp only [category.id_comp, category.comp_id, Completion_map_apply],
        dsimp only [cosimplicial_object.augmented.to_cocomplex_d,
          cosimplicial_object.augmented.drop, comma.snd, cosimplicial_object.whiskering,
          whiskering_right, cosimplicial_object.coboundary, LCC],
        rw [← Completion_map_apply, Completion.map_sum],
        congr,
        funext k,
        rw [Completion.map_gsmul],
        congr' 1,
        apply FLC_iso_helper },
      { exfalso,
        apply hh,
        refl }
    end,
  is_strict := λ i, { strict_hom' := λ a, by { cases i; refl } } }

include surj

theorem prop819 {m : ℕ} (ε : ℝ≥0) (hε : 0 < ε)
  (f : (FLC F M).X (m+1)) (hf : (FLC F M).d (m+1) (m+2) f = 0) :
  ∃ g : (FLC F M).X m, (FLC F M).d m (m+1) g = f ∧ nnnorm g ≤ (1 + ε) * (nnnorm f) :=
begin
  apply exact_of_strict_iso _ _ (FLC_iso F M) ε hε _ _ _ hf,
  apply cmpl_exact_of_exact _ _ hε,
  clear hf f m hε ε,
  intros n f hf,
  -- We've reduced to the non-completed case.
  sorry,
end
