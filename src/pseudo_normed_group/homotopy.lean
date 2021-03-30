import pseudo_normed_group.system_of_complexes
import pseudo_normed_group.rescale

.

noncomputable theory

universe variables u

open_locale nnreal

open differential_object.complex_like

/-

variables {BD BD₁ BD₂ : breen_deligne.data} (f g : BD₁ ⟶ BD₂)
variables (h : homotopy f g)

variables (c' c₁' c₂' : ℕ → ℝ≥0)
variables [BD.suitable c'] [BD₁.suitable c₁'] [BD₂.suitable c₂']
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0)

namespace breen_deligne

section homotopy

open differential_object differential_object.complex_like

def BD_map [∀ i, (f.f i).suitable (c₁' i) (c₂' i)] :
  BD₂.complex c₂' r V r' M c ⟶ BD₁.complex c₁' r V r' M c :=
hom.mk' (λ i, ((f.f i).eval_CLCFPTinv r V r' (c * c₁' i) (c * c₂' i)).app _)
begin
  dsimp [coherent_indices],
  intros i j hij, subst j,
  erw [cochain_complex.mk'_d', cochain_complex.mk'_d'],
  dsimp only [data.complex_d],
  erw [← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _,
       ← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _],
  { congr' 1, have := f.comm (i+1) i, exact this.symm },
  { exact universal_map.suitable.comp (c * c₁' i) },
  { exact universal_map.suitable.comp (c * c₂' (i+1)) }
end

variables {f g}

def homotopy [∀ i, (f.f i).suitable (c₁' i) (c₂' i)] [∀ i, (g.f i).suitable (c₁' i) (c₂' i)]
  [∀ j i, (h.h j i).suitable (c₁' j) (c₂' i)] :
  homotopy (BD_map f c₁' c₂' r V M c) (BD_map g c₁' c₂' r V M c) :=
{ h := λ j i, (h.h i j).eval_CLCFPTinv r V r' M (c * c₁' i) (c * c₂' j),
  h_eq_zero := λ i j hij,
  begin
    convert universal_map.eval_CLCFPTinv_zero r V r' M _ _,
    rw h.h_eq_zero,
    exact ne.symm hij
  end,
  comm :=
  begin
    simp only [htpy_idx_rel₁_tt_nat, htpy_idx_rel₂_tt_nat],
    rintro i j k rfl,
    simp only [nat.succ_ne_zero i, nat.succ_eq_add_one, false_and, or_false],
    rintro rfl,
    erw [cochain_complex.mk'_d', cochain_complex.mk'_d'],
    dsimp only [data.complex_d],
    erw [← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _,
        ← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _],
    swap, { exact universal_map.suitable.comp (c * c₂' (i+1+1)) },
    swap, { exact universal_map.suitable.comp (c * c₁' i) },
    sorry
  end }

end homotopy

section rescale

-- move this
def rescale_constants (c' : ℕ → ℝ≥0) (N : ℝ≥0) : ℕ → ℝ≥0 :=
λ i, (c' i) * N⁻¹

-- warning: this might need `[fact (0 < N)]`
instance rescale_constants_suitable (N : ℝ≥0) :
  BD.suitable (rescale_constants c' N) :=
sorry

variables (BD)

open differential_object.complex_like category_theory
open ProFiltPseuNormGrpWithTinv (of)

open normed_group_hom

lemma aux₀ (c c' N : ℝ≥0) : fact (c * c' * N⁻¹ ≤ c * (c' * N⁻¹)) :=
by simpa only [mul_assoc] using nnreal.fact_le_refl _

lemma aux₀' (c c' N : ℝ≥0) : fact (r' * (c * c') * N⁻¹ ≤ r' * (c * (c' * N⁻¹))) :=
by simpa only [mul_assoc] using nnreal.fact_le_refl _

local attribute [instance] aux₀ aux₀'

def rescale_hom (c c' N : ℝ≥0) (n : ℕ) :
  CLCFPTinv r V r' M (c * (c' * N⁻¹)) n ⟶ CLCFPTinv r V r' (rescale N M) (c * c') n :=
equalizer.map (CLCFP.res V r' _ _ _) (CLCFP.res V r' _ _ _)
sorry
begin
  sorry
end

-- this is not `iso.refl` -- so close, and yet so far away
-- the difference is `M_{(c * c_i) * N⁻¹}` vs `M_{c * (c_i * N⁻¹)}`
def complex_rescale_iso_X (N : ℝ≥0) (i : ℕ) :
  (BD.complex (rescale_constants c' N) r V r' M c).X i ≅
  (BD.complex c' r V r' (of r' $ rescale N M) c).X i :=
{ hom := rescale_hom _ _ _ _ _ _ _,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

-- this is not `iso.refl` -- so close, and yet so far away
-- the difference is `M_{(c * c_i) * N⁻¹}` vs `M_{c * (c_i * N⁻¹)}`
def complex_rescale_iso (N : ℝ≥0) :
  BD.complex (rescale_constants c' N) r V r' M c ≅
  BD.complex c' r V r' (of r' $ rescale N M) c :=
iso_of_components (complex_rescale_iso_X _ _ _ _ _ _ _)
begin
  sorry
end

variable (N : ℝ≥0)
open pseudo_normed_group

set_option pp.implicit true
example : (filtration (rescale N M) c : Type*) = filtration M (c * N⁻¹) := rfl
theorem foo (n) : CLCFP V r' (rescale N M) c n = CLCFP V r' M (c * N⁻¹) n := rfl
theorem bar (n) :
  (CLCFP.Tinv V r' c n : CLCFP V r' (rescale N M) c n ⟶ CLCFP V r' M (r' * c * N⁻¹) n) =
  ((CLCFP.Tinv V r' (c * N⁻¹) n : CLCFP V r' M (c * N⁻¹) n ⟶ CLCFP V r' M (r' * (c * N⁻¹)) n) ≫
    (CLCFP.res _ _ _ _ _ : CLCFP V r' M (r' * (c * N⁻¹)) n ⟶ CLCFP V r' M (r' * c * N⁻¹) n)) :=
begin
  dsimp [CLCFP.Tinv_def],
  have := (CLCFP.Tinv'_of_hom V r' c M _ _).symm,

end

-- theorem baz (n) :
--   (CLCFP.Tinv' V r' c n : CLCFP V r' (rescale N M) c n ⟶ CLCFP V r' M (r' * c * N⁻¹) n) =
--   ((CLCFP.Tinv' V r' (c * N⁻¹) n : CLCFP V r' M (c * N⁻¹) n ⟶ CLCFP V r' M (r' * (c * N⁻¹)) n) ≫
--     (eq_to_hom (by rw mul_assoc) : CLCFP V r' M (r' * (c * N⁻¹)) n ⟶ CLCFP V r' M (r' * c * N⁻¹) n)) :=
-- _.

-- begin
--   suffices :
--     (CLCFP.Tinv' V r' c n : CLCFP V r' (rescale N M) c n ⟶ CLCFP V r' M (r' * c * N⁻¹) n) =
--     ((CLCFP.Tinv V r' (c * N⁻¹) n : CLCFP V r' M (c * N⁻¹) n ⟶ CLCFP V r' M (r' * (c * N⁻¹)) n) ≫
--       (eq_to_hom (by rw mul_assoc) : CLCFP V r' M (r' * (c * N⁻¹)) n ⟶ CLCFP V r' M (r' * c * N⁻¹) n)),


-- end
-- theorem bar (n) :
--   (LCFP.Tinv V r' c n : LCFP V r' (rescale N M) c n ⟶ LCFP V r' M (r' * c * N⁻¹) n) =
--   ((LCFP.Tinv V r' (c * N⁻¹) n : LCFP V r' M (c * N⁻¹) n ⟶ LCFP V r' M (r' * (c * N⁻¹)) n) ≫
--     (eq_to_hom (by rw mul_assoc) : LCFP V r' M (r' * (c * N⁻¹)) n ⟶ LCFP V r' M (r' * c * N⁻¹) n)) :=
-- begin
-- end

example (n) : CLCFPTinv r V r' (rescale N M) c n ≅ CLCFPTinv r V r' M (c * N⁻¹) n :=
begin
  unfold CLCFPTinv,
  dsimp only [foo],
  apply eq_to_iso,
  -- congr,
end

example (n) :
  BD.complex_X (rescale_constants c' N) r V r' M c n ≅
  BD.complex_X c' r V r' (of r' $ rescale N M) c n :=
begin

end

#print rescale.pseudo_normed_group
#check (by apply_instance : pseudo_normed_group (rescale N M))
#print Tx

end rescale

section double

variables (BD)

open ProFiltPseuNormGrpWithTinv (of)

open category_theory

instance double_suitable : BD.double.suitable c' :=
sorry

-- === !!! warning, the instance for `M × M` has sorry'd data
def double_iso_prod :
  BD.double.complex c' r V r' M c ≅ BD.complex c' r V r' (of r' $ M × M) c :=
sorry

example (N : ℝ≥0) :
  BD.double.complex (rescale_constants c' N) r V r' M c ≅
  BD.complex c' r V r' (of r' $ rescale N (M × M)) c :=
(double_iso_prod BD _ r V _ c) ≪≫ (complex_rescale_iso _ _ _ _ _ _ _)

end double

end breen_deligne

-/
