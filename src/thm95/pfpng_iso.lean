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

open comphaus_filtered_pseudo_normed_group

@[simps {fully_applied := ff}]
def Pow_mul_comm_obj_equiv (X : ProFiltPseuNormGrpWithTinv r') :
  X ^ (m * n) ≃+ X ^ (n * m) :=
(linear_map.fun_congr_left ℤ X $
calc fin (n * m) ≃ fin n × fin m : fin_prod_fin_equiv.symm
      ... ≃ fin m × fin n            : equiv.prod_comm _ _
      ... ≃ fin (m * n)              : fin_prod_fin_equiv).to_add_equiv

lemma Pow_mul_comm_obj_equiv_strict
  (X : ProFiltPseuNormGrpWithTinv r') (c : ℝ≥0) (x : (X : Type _) ^ (m * n)) :
  x ∈ pseudo_normed_group.filtration ↥(of r' (↥X ^ (m * n))) c ↔
   (Pow_mul_comm_obj_equiv r' m n X) x ∈ pseudo_normed_group.filtration (↥X ^ (n * m)) c :=
begin
  intros,
  simp only [Pow_mul_comm_obj_equiv_apply,
    linear_equiv.trans_apply, linear_equiv.coe_to_add_equiv,
    linear_map.fun_congr_left_apply, linear_map.fun_congr_left_comp],
  erw pseudo_normed_group.mem_filtration_pi, -- TODO arrange so that `simp` can achieve this
  erw pseudo_normed_group.mem_filtration_pi,
  fsplit,
  { intros h i,
    apply h, },
  { intros h i,
    simpa using h (fin_prod_fin_equiv ((fin_prod_fin_equiv.symm) i).swap), }
end

lemma Pow_mul_comm_obj_equiv_ctu (X : ProFiltPseuNormGrpWithTinv r') (c : ℝ≥0) :
  continuous (pseudo_normed_group.level ⇑(Pow_mul_comm_obj_equiv r' m n X)
    (λ c x, (Pow_mul_comm_obj_equiv_strict r' _ _ X c x).mp) c) :=
begin
  rw [← (filtration_pi_homeo _ c).comp_continuous_iff,
    ← (filtration_pi_homeo _ c).symm.comp_continuous_iff'],
  apply continuous_pi,
  intro i,
  dsimp,
  convert continuous_apply (fin_prod_fin_equiv ((fin_prod_fin_equiv.symm) i).swap) using 1,
  ext x,
  rw subtype.coe_mk,
end

@[simps {fully_applied := ff}]
def Pow_mul_comm_obj (X : ProFiltPseuNormGrpWithTinv r') :
  of r' (X ^ (m * n)) ≅ of r' (X ^ (n * m)) :=
iso_of_equiv_of_strict' (Pow_mul_comm_obj_equiv r' _ _ X)
  (Pow_mul_comm_obj_equiv_strict r' _ _ X)
  (Pow_mul_comm_obj_equiv_ctu r' _ _ X)
  (by { intros, ext, refl })

def Pow_mul_comm : Pow r' (m * n) ≅ Pow r' (n * m) :=
  nat_iso.of_components
  (λ X, Pow_mul_comm_obj r' _ _ X)
  begin
    intros X Y f, ext x i,
    -- This is just a terminal simp, which I've exploded for the sake of speed.
    simp only [Pow_mul_comm_obj_hom_to_fun,
      ProFiltPseuNormGrpWithTinv.iso_of_equiv_of_strict'_hom_apply,
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

lemma Pow_rescale_aux_ctu
  (X : ProFiltPseuNormGrpWithTinv r') (c' : ℝ≥0) :
  continuous (pseudo_normed_group.level ⇑(Pow_rescale_aux r' c m X) (λ _ _, id) c') :=
begin
  erw [← (filtration_pi_homeo _ _).comp_continuous_iff,
    ← (filtration_pi_homeo _ _).symm.comp_continuous_iff'],
  apply continuous_pi,
  intro i,
  dsimp,
  convert continuous_apply i,
  ext,
  rw subtype.coe_mk
end

def Pow_rescale : Pow r' m ⋙ rescale r' c ≅ rescale r' c ⋙ Pow r' m :=
nat_iso.of_components
  (λ X, begin
    dsimp,
    fapply iso_of_equiv_of_strict',
    apply Pow_rescale_aux,
    { intros c' x,
      erw pseudo_normed_group.mem_filtration_pi, }, -- err, why does that close the goal?
    { apply Pow_rescale_aux_ctu },
    { intros x, ext i, refl, },
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
