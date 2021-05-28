import pseudo_normed_group.category
import rescale.pseudo_normed_group
.

open_locale nnreal
local attribute [instance] type_pow
noncomputable theory

open category_theory

namespace ProFiltPseuNormGrpWithTinv

variables (r' : ℝ≥0) [fact (0 < r')]
variables (c : ℝ≥0) (m n : ℕ)
variables (M : ProFiltPseuNormGrpWithTinv r')

local notation `ρ` := _root_.rescale

/-
Useful facts that we already have:

* `Pow_mul (r') (N n : ℕ) : Pow r' (N * n) ≅ Pow r' N ⋙ Pow r' n`
* `iso_of_equiv_of_strict'` for constructing isos in `ProFiltPseuNormGrpWithTinv r'`
-/

def Pow_mul_comm : Pow r' (m * n) ≅ Pow r' (n * m) :=
  nat_iso.of_components
  (λ X, begin
    dsimp,
    fapply iso_of_equiv_of_strict',
    apply (linear_map.fun_congr_left ℤ X _).to_add_equiv,
    calc fin (n * m) ≃ fin n × fin m : fin_prod_fin_equiv.symm
      ... ≃ fin (m * n) : sorry,
    sorry,
    sorry,
    sorry,
  end)
  sorry

def Pow_comm : Pow r' m ⋙ Pow r' n ≅ Pow r' n ⋙ Pow r' m :=
calc Pow r' m ⋙ Pow r' n ≅ Pow r' (m * n) : (Pow_mul r' m n).symm
  ... ≅ Pow r' (n * m)                    : Pow_mul_comm r' m n
  ... ≅ Pow r' n ⋙ Pow r' m               : Pow_mul r' n m

def Pow_rescale : Pow r' m ⋙ rescale r' c ≅ rescale r' c ⋙ Pow r' m :=
nat_iso.of_components
  (λ X, begin
    dsimp,
    fapply iso_of_equiv_of_strict',
    sorry,
    sorry,
    sorry,
    sorry,
  end)
  sorry

/-- A very specific isomorphism -/
def Pow_rescale_Pow_iso :
  Pow r' m ⋙ rescale r' c ⋙ Pow r' n ≅ Pow r' n ⋙ Pow r' m ⋙ rescale r' c :=
calc Pow r' m ⋙ rescale r' c ⋙ Pow r' n
      ≅ Pow r' m ⋙ Pow r' n ⋙ rescale r' c : iso_whisker_left (Pow r' m) (Pow_rescale r' c n).symm
  ... ≅ (Pow r' m ⋙ Pow r' n) ⋙ rescale r' c : (functor.associator _ _ _).symm
  ... ≅ (Pow r' n ⋙ Pow r' m) ⋙ rescale r' c : iso_whisker_right (Pow_comm r' m n) _
  ... ≅ Pow r' n ⋙ Pow r' m ⋙ rescale r' c : functor.associator _ _ _

end ProFiltPseuNormGrpWithTinv
