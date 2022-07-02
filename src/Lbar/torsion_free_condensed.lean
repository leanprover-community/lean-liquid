import Lbar.torsion_free_profinite
import condensed.condensify

noncomputable theory

universe u

open category_theory opposite

open_locale nnreal

namespace Lbar

variables (r' : ℝ≥0) [fact (0 < r')]

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
condensify (Fintype_Lbar.{u u} r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r')

instance (S : Profinite.{u}) (T : ExtrDisc.{u}) :
  no_zero_smul_divisors ℤ (((condensed.{u} r').obj S).val.obj (op T.val)) :=
sorry

end Lbar
