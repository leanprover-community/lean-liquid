import polyhedral_lattice.Hom
import Lbar.pseudo_normed_group

import normed_spectral

import pseudo_normed_group.homotopy

import thm95.double_complex
import thm95.constants

noncomputable theory

universe variable u

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.

open polyhedral_lattice opposite
open thm95.universal_constants system_of_double_complexes category_theory breen_deligne
open ProFiltPseuNormGrpWithTinv (of)

section

variables (BD : package)
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : SemiNormedGroup.{u}) [normed_with_aut r V]
variables (κ κ' : ℕ → ℝ≥0) [BD.data.very_suitable r r' κ]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')
variables (m : ℕ)
variables (Λ : PolyhedralLattice.{u})

def NSH_aux_type (N : ℕ) (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :=
normed_spectral_homotopy
  ((BD_system_map (BD.data.sum (2^N)) κ (rescale_constants κ (2^N)) r V).app M)
  m (k' κ' m) (ε r r' BD κ' m) (c₀ r r' BD κ κ' m Λ) (H r r' BD κ' m)

section

variables {BD r r' V κ κ' m}

section NSH_h

variables [package.adept BD κ κ']

def NSH_h {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (q q' : ℕ) (c : ℝ≥0) :
  ((BD.data.system κ r V r').obj M) (k' κ' m * c) q' ⟶
    ((((data.mul (2 ^ N₂ r r' BD κ' m)).obj BD.data).system
      (rescale_constants κ (2 ^ N₂ r r' BD κ' m)) r V r').obj M) c q :=
if hqm : q' ≤ m + 1
then
begin
  refine (universal_map.eval_CLCFPTinv _ _ _ _ _ _).app _,
  { exact (data.homotopy_mul BD.data BD.homotopy (N₂ r r' BD κ' m)).hom q q' },
  { dsimp,
    refine universal_map.suitable.le _ _ (c * (κ' q' * κ q')) _
      infer_instance le_rfl _,
    calc c * (κ' q' * κ q')
        = κ' q' * (c * κ q') : mul_left_comm _ _ _
    ... ≤ k' κ' m * (c * κ q') : mul_le_mul' (κ'_le_k' _ _ hqm) le_rfl
    ... = k' κ' m * c * κ q' : (mul_assoc _ _ _).symm, }
end
else 0

lemma norm_NSH_h_le {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (q : ℕ) (hqm : q ≤ m) (c : ℝ≥0) :
  ∥@NSH_h BD r r' _ _ _ _ V _ κ κ' _ m _ M q (q+1) c∥ ≤ (H r r' BD κ' m) :=
begin
  rw [NSH_h, dif_pos (nat.succ_le_succ hqm)],
  apply universal_map.norm_eval_CLCFPTinv₂_le,
  exact (bound_by_H r r' BD κ' _ hqm),
end

end NSH_h

instance NSH_δ_res' (N i : ℕ) (c : ℝ≥0) [hN : fact (k' κ' m ≤ 2 ^ N)] :
  fact (k' κ' m * c * rescale_constants κ (2 ^ N) i ≤ c * κ i) :=
begin
  refine ⟨_⟩,
  calc k' κ' m * c * (κ i * (2 ^ N)⁻¹)
     = (k' κ' m * (2 ^ N)⁻¹) * (c * κ i) : by ring1
  ... ≤ 1 * (c * κ i) : mul_le_mul' _ le_rfl
  ... = c * κ i : one_mul _,
  apply mul_inv_le_of_le_mul,
  rw one_mul,
  exact hN.1
end

variables (κ')

@[simps f]
def NSH_δ_res {BD : data} [BD.suitable κ] {r r' : ℝ≥0}
  [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] {V : SemiNormedGroup.{u}} [normed_with_aut r V]
  (N : ℕ) [fact (k' κ' m ≤ 2 ^ N)] (c : ℝ≥0) {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} :
  ((BD.system κ r V r').obj M).obj (op c) ⟶
    ((BD.system (rescale_constants κ (2 ^ N)) r V r').obj M).obj (op (k' κ' m * c)) :=
{ f := λ i, (@CLCFPTinv.res r V _ _ r' _ _ _ _ _ (NSH_δ_res' _ _ _)).app M,
  comm' :=
  begin
    intros i j hij,
    dsimp [data.system_obj, data.complex],
    exact nat_trans.congr_app (universal_map.res_comp_eval_CLCFPTinv r V r' _ _ _ _ _) M,
  end }
.

variables {κ'}

def NSH_δ {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (c : ℝ≥0) :
  ((BD.data.system κ r V r').obj M).obj (op c) ⟶
    ((((data.mul (2 ^ N₂ r r' BD κ' m)).obj BD.data).system
      (rescale_constants κ (2 ^ N₂ r r' BD κ' m)) r V r').obj M).obj (op (k' κ' m * c)) :=
NSH_δ_res κ' (N₂ r r' BD κ' m) _ ≫ (BD_map (BD.data.proj (2 ^ N₂ r r' BD κ' m)) _ _ r V _).app M

lemma norm_NSH_δ_le {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (c : ℝ≥0) (q : ℕ) :
  ∥(@NSH_δ BD r r' _ _ _ _ V _ κ κ' _ m M c).f q∥ ≤ (ε r r' BD κ' m) :=
begin
  refine le_trans (normed_group_hom.norm_comp_le_of_le'
    (r ^ (b r r' BD κ' m)) (N r r' BD κ' m) _ (mul_comm _ _) _ _) _,
  { apply universal_map.norm_eval_CLCFPTinv₂_le,
    apply universal_map.proj_bound_by },
  { refine @CLCFPTinv.norm_res_le_pow r V _ _ r' _ _ _ _ _ _ _ ⟨_⟩ _,
    dsimp only [unop_op, rescale_constants],
    simp only [← mul_assoc, mul_right_comm _ c],
    simp only [mul_right_comm _ (κ q)],
    refine mul_le_mul' _ le_rfl,
    refine mul_le_mul' _ le_rfl,
    apply thm95.universal_constants.N₂_spec, },
  { apply_mod_cast r_pow_b_le_ε }
end

variables (V κ' m)

open homological_complex category_theory.preadditive

end

variables [package.adept BD κ κ']

def NSH_aux' (M) (hδ) : NSH_aux_type BD r r' V κ κ' m Λ (N₂ r r' BD κ' m) M :=
{ h := λ q q' c, NSH_h q q' c,
  norm_h_le := by { rintro q q' hqm rfl c hc, rw nnreal.coe_nat_cast, exact norm_NSH_h_le q hqm c },
  δ := NSH_δ,
  hδ := hδ,
  norm_δ_le := λ c hc q hqm, by apply norm_NSH_δ_le }
.

def NSH_aux (M) : NSH_aux_type BD r r' V κ κ' m Λ (N₂ r r' BD κ' m) M :=
NSH_aux' BD r r' V κ κ' m Λ M
begin
  introsI c hc q hqm,
  haveI hqm_ : fact (q ≤ m) := ⟨hqm⟩,
  rw [NSH_δ, NSH_h, NSH_h, dif_pos (nat.succ_le_succ hqm), dif_pos (hqm.trans (nat.le_succ _))],
  erw [homological_complex.comp_f],
  dsimp only [unop_op, NSH_δ_res_f, data.system_res_def, quiver.hom.apply,
    BD_system_map_app_app, BD_map_app_f, data.system_obj_d],
  simp only [← universal_map.eval_CLCFPTinv_def],
  have hcomm := (data.homotopy_mul BD.data BD.homotopy (N₂ r r' BD κ' m)).comm q,
  simp only [universal_map.res_comp_eval_CLCFPTinv_absorb, hcomm, ← nat_trans.app_add, add_assoc,
    ← nat_trans.comp_app, ← category.assoc, ← universal_map.eval_CLCFPTinv_comp,
    universal_map.eval_CLCFPTinv_comp_res_absorb, ← universal_map.eval_CLCFPTinv_add],
  congr' 2,
  rw [← add_assoc, add_comm, @prev_d_eq _ _ _ _ _ _ _ _ q (q+1)],
  swap, { dsimp, refl },
  congr' 1,
  rw add_comm,
  congr' 1,
  rw d_next_nat,
end
.

end
