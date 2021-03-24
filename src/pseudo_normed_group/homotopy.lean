import pseudo_normed_group.system_of_complexes

.

noncomputable theory

universe variables u

open_locale nnreal

open differential_object.complex_like

variables {BD₁ BD₂ : breen_deligne.data} (f g : BD₁ ⟶ BD₂)
variables (h : homotopy f g)

variables (c₁' c₂' : ℕ → ℝ≥0) [BD₁.suitable c₁'] [BD₂.suitable c₂']
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0)

namespace breen_deligne

open differential_object differential_object.complex_like

def BD_map [∀ i, (f.f i).suitable (c₁' i) (c₂' i)] :
  BD₂.complex c₂' r V r' M c ⟶ BD₁.complex c₁' r V r' M c :=
hom.mk' (λ i, (f.f i).eval_CLCFPTinv r V r' M (c * c₁' i) (c * c₂' i))
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

end breen_deligne
