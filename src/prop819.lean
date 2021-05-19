import for_mathlib.Cech.split
import for_mathlib.Profinite.functorial_limit
import for_mathlib.simplicial.complex
import locally_constant.Vhat
import for_mathlib.simplicial.right_op

open_locale nnreal

noncomputable theory

open category_theory
open SemiNormedGroup

universes u

-- We have a surjective morphism of profinite sets.
variables (F : arrow Profinite.{u}) (surj : function.surjective F.hom)
variables (M : SemiNormedGroup.{u})

abbreviation FLC : cochain_complex SemiNormedGroup ℕ :=
  ((cosimplicial_object.augmented.map (LCC.{u u}.obj M)).obj
  F.augmented_cech_nerve.right_op).to_cocomplex

theorem prop819 {m : ℕ} (c ε : ℝ≥0) (hε : 0 < ε)
  (f : (FLC F M).X (m+1)) (hf : (FLC F M).d (m+1) (m+2) f = 0)
  (hfnorm : nnnorm f ≤ c) :
  ∃ g : (FLC F M).X m, (FLC F M).d m _ g = f ∧ nnnorm g ≤ (1 + ε) * c := sorry
