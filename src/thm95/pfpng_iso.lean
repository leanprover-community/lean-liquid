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
      ... ≃ fin m × fin n            : equiv.prod_comm _ _
      ... ≃ fin (m * n)              : fin_prod_fin_equiv,
    { intros,
      simp only [linear_equiv.trans_apply, linear_equiv.coe_to_add_equiv,
        linear_map.fun_congr_left_apply, linear_map.fun_congr_left_comp],
      erw pseudo_normed_group.mem_filtration_pi, -- TODO arrange so that `simp` can achieve this
      erw pseudo_normed_group.mem_filtration_pi,
      fsplit,
      { intros h i,
        apply h, },
      { intros h i,
        simpa using h (fin_prod_fin_equiv ((fin_prod_fin_equiv.symm) i).swap), } },
    { intro c, sorry, },
    { intro x, ext i,
      -- This is just a terminal simp, which I've exploded for the sake of speed.
      simp only [linear_equiv.trans_apply, linear_map.fun_left_apply, linear_equiv.coe_to_add_equiv,
        equiv.prod_comm_apply, linear_map.fun_congr_left_apply, linear_map.fun_congr_left_comp,
        profinitely_filtered_pseudo_normed_group_with_Tinv.pi_Tinv_apply], },
  end)
  begin
    intros X Y f, ext x i,
    -- This is just a terminal simp, which I've exploded for the sake of speed.
    simp only [ProFiltPseuNormGrpWithTinv.iso_of_equiv_of_strict'_hom_apply,
      ProFiltPseuNormGrpWithTinv.Pow_map, linear_equiv.trans_apply,
      ProFiltPseuNormGrpWithTinv.coe_comp_apply,
      linear_map.fun_left_apply, linear_equiv.coe_to_add_equiv, id.def,
      equiv.prod_comm_apply, linear_map.fun_congr_left_apply, linear_map.fun_congr_left_comp,
      profinitely_filtered_pseudo_normed_group_with_Tinv.pi_map_to_fun],
  end

def Pow_comm : Pow r' m ⋙ Pow r' n ≅ Pow r' n ⋙ Pow r' m :=
calc Pow r' m ⋙ Pow r' n ≅ Pow r' (m * n) : (Pow_mul r' m n).symm
  ... ≅ Pow r' (n * m)                    : Pow_mul_comm r' m n
  ... ≅ Pow r' n ⋙ Pow r' m               : Pow_mul r' n m

@[simps]
def Pow_rescale_aux (c : ℝ≥0) (m : ℕ)
  (X : ProFiltPseuNormGrpWithTinv r') :
  ρ c (X ^ m) ≃+ (ρ c X) ^ m :=
add_equiv.refl _

def Pow_rescale : Pow r' m ⋙ rescale r' c ≅ rescale r' c ⋙ Pow r' m :=
nat_iso.of_components
  (λ X, begin
    dsimp,
    fapply iso_of_equiv_of_strict',
    apply Pow_rescale_aux,
    { intros c' x,
      erw pseudo_normed_group.mem_filtration_pi, }, -- err, why does that close the goal?
    { intros c', sorry, },
    { intros x, ext i, dsimp,
      -- refl, -- seems to perhaps work here, but very slow.
      sorry,
      },
  end)
  begin
    intros X Y f, ext x i,
    dsimp,
    refl,
  end

/-- A very specific isomorphism -/
def Pow_rescale_Pow_iso :
  Pow r' m ⋙ rescale r' c ⋙ Pow r' n ≅ Pow r' n ⋙ Pow r' m ⋙ rescale r' c :=
calc Pow r' m ⋙ rescale r' c ⋙ Pow r' n
      ≅ Pow r' m ⋙ Pow r' n ⋙ rescale r' c : iso_whisker_left (Pow r' m) (Pow_rescale r' c n).symm
  ... ≅ (Pow r' m ⋙ Pow r' n) ⋙ rescale r' c : (functor.associator _ _ _).symm
  ... ≅ (Pow r' n ⋙ Pow r' m) ⋙ rescale r' c : iso_whisker_right (Pow_comm r' m n) _
  ... ≅ Pow r' n ⋙ Pow r' m ⋙ rescale r' c : functor.associator _ _ _

end ProFiltPseuNormGrpWithTinv
