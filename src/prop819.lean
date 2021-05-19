import for_mathlib.Cech.split
import for_mathlib.Profinite.functorial_limit
import for_mathlib.simplicial.complex
import for_mathlib.SemiNormedGroup
import locally_constant.Vhat

open_locale nnreal

noncomputable theory

open category_theory
open SemiNormedGroup

universes u

-- We have a surjective morphism of profinite sets.
variables (F : arrow Profinite.{u}) (surj : function.surjective F.hom)
variables (M : SemiNormedGroup.{u})

abbreviation FLC : cochain_complex SemiNormedGroup ℕ :=
  (((cosimplicial_object.augmented.whiskering _ _).obj (LCC.{u u}.obj M)).obj
  F.augmented_cech_nerve.right_op).to_cocomplex

include surj

theorem prop819 {m : ℕ} (ε : ℝ≥0) (hε : 0 < ε)
  (f : (FLC F M).X m) (hf : (FLC F M).d_from m f = 0) :
  ∃ g : (FLC F M).X_prev m, (FLC F M).d_to m g = f ∧ nnnorm g ≤ (1 + ε) * (nnnorm f) := sorry
