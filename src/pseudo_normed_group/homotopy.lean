import pseudo_normed_group.system_of_complexes
import rescale.CLC

.

noncomputable theory

universe variables u

open_locale nnreal

open differential_object.complex_like

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

-- def BD_map [∀ i, (f.f i).suitable (c₁' i) (c₂' i)] :
--   BD₂.complex c₂' r V r' M c ⟶ BD₁.complex c₁' r V r' M c :=
-- hom.mk' (λ i, ((f.f i).eval_CLCFPTinv r V r' (c * c₁' i) (c * c₂' i)).app _)
-- begin
--   dsimp [coherent_indices],
--   intros i j hij, subst j,
--   erw [cochain_complex.mk'_d', cochain_complex.mk'_d'],
--   dsimp only [data.complex_d],
--   erw [← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _,
--        ← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _],
--   { congr' 1, have := f.comm (i+1) i, exact this.symm },
--   { exact universal_map.suitable.comp (c * c₁' i) },
--   { exact universal_map.suitable.comp (c * c₂' (i+1)) }
-- end

variables {f g}

-- def homotopy [∀ i, (f.f i).suitable (c₁' i) (c₂' i)] [∀ i, (g.f i).suitable (c₁' i) (c₂' i)]
--   [∀ j i, (h.h j i).suitable (c₁' j) (c₂' i)] :
--   homotopy (BD_map f c₁' c₂' r V M c) (BD_map g c₁' c₂' r V M c) :=
-- { h := λ j i, (h.h i j).eval_CLCFPTinv r V r' M (c * c₁' i) (c * c₂' j),
--   h_eq_zero := λ i j hij,
--   begin
--     convert universal_map.eval_CLCFPTinv_zero r V r' M _ _,
--     rw h.h_eq_zero,
--     exact ne.symm hij
--   end,
--   comm :=
--   begin
--     simp only [htpy_idx_rel₁_tt_nat, htpy_idx_rel₂_tt_nat],
--     rintro i j k rfl,
--     simp only [nat.succ_ne_zero i, nat.succ_eq_add_one, false_and, or_false],
--     rintro rfl,
--     erw [cochain_complex.mk'_d', cochain_complex.mk'_d'],
--     dsimp only [data.complex_d],
--     erw [← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _,
--         ← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _],
--     swap, { exact universal_map.suitable.comp (c * c₂' (i+1+1)) },
--     swap, { exact universal_map.suitable.comp (c * c₁' i) },
--     sorry
--   end }

end homotopy

section rescale

-- move this
def rescale_constants (c' : ℕ → ℝ≥0) (N : ℝ≥0) : ℕ → ℝ≥0 :=
λ i, (c' i) * N⁻¹

-- warning: this might need `[fact (0 < N)]`
instance rescale_constants_suitable (N : ℝ≥0) :
  BD.suitable (rescale_constants c' N) :=
by { delta rescale_constants, apply_instance }

variables (BD)

open opposite ProFiltPseuNormGrpWithTinv (of)

-- this is not `iso.refl` -- so close, and yet so far away
-- the difference is `M_{(c * c_i) * N⁻¹}` vs `M_{c * (c_i * N⁻¹)}`
theorem complex_rescale_eq (N : ℝ≥0) :
  (BD.complex (rescale_constants c' N) r V r' c).obj (op M) =
  (BD.complex c' r V r' c).obj (op $ of r' $ rescale N M) :=
begin
  dsimp only [data.complex, rescale_constants],
  haveI : ∀ c c', fact (c * c' * N⁻¹ ≤ c * (c' * N⁻¹)) :=
    λ c c', by simpa only [mul_assoc] using nnreal.fact_le_refl _,
  transitivity
    (BD.complex₂ r V r' (λ (i : ℕ), c * c' i * N⁻¹) (λ (i : ℕ), r' * (c * c' i) * N⁻¹)).obj (op $ of r' M),
  { simp only [mul_assoc, ProFiltPseuNormGrpWithTinv.of_coe] },
  refine cochain_complex.ext (λ i, _),
  dsimp only [data.complex₂, rescale_constants, data.complex₂_d, universal_map.eval_CLCFPTinv₂,
    _root_.id, NormedGroup.equalizer.map_nat_app],
  refine NormedGroup.equalizer.map_congr _ _ rfl rfl rfl rfl,
  { simp only [universal_map.eval_CLCFP_rescale V r' _ _ _ _ (BD.d (succ i) i) N M] },
  { simp only [universal_map.eval_CLCFP_rescale V r' _ _ _ _ (BD.d (succ i) i) N M] },
end

end rescale

section double

variables (BD)

open ProFiltPseuNormGrpWithTinv (of)

open category_theory

-- instance double_suitable : BD.double.suitable c' :=
-- sorry

-- -- === !!! warning, the instance for `M × M` has sorry'd data
-- def double_iso_prod :
--   BD.double.complex c' r V r' M c ≅ BD.complex c' r V r' (of r' $ M × M) c :=
-- sorry

-- example (N : ℝ≥0) :
--   BD.double.complex (rescale_constants c' N) r V r' M c ≅
--   BD.complex c' r V r' (of r' $ rescale N (M × M)) c :=
-- (double_iso_prod BD _ r V _ c) ≪≫ (complex_rescale_iso _ _ _ _ _ _ _)

end double

end breen_deligne
