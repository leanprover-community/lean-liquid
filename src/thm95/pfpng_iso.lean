import pseudo_normed_group.category
import rescale.pseudo_normed_group
.

open_locale nnreal
local attribute [instance] type_pow

open category_theory

namespace ProFiltPseuNormGrpWithTinv

variables (r' : ℝ≥0) [fact (0 < r')]
variables (c : ℝ≥0) (m n : ℕ)
variables (M : ProFiltPseuNormGrpWithTinv r')

local notation `ρ` := _root_.rescale

/-
Useful facts that we already have:

* `Pow_mul (N n : ℕ) : Pow r' (N * n) ≅ Pow r' N ⋙ Pow r' n`
* `iso_of_equiv_of_strict'` for constructing isos in `ProFiltPseuNormGrpWithTinv r'`
-/

/-- A very specific isomorphism -/
def Pow_rescale_Pow_iso :
  Pow r' m ⋙ rescale r' c ⋙ Pow r' n ≅ Pow r' n ⋙ Pow r' m ⋙ rescale r' c :=
sorry

end ProFiltPseuNormGrpWithTinv
