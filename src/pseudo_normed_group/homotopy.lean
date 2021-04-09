import pseudo_normed_group.system_of_complexes
import rescale.Tinv
/-!

*TODO*: find someone who can explain what is going on in this file. There
are no docstrings, sorried data and false assumptions.

-/

noncomputable theory

universe variables u

open_locale nnreal

open category_theory differential_object.complex_like

namespace breen_deligne

variables {BD BD₁ BD₂ : breen_deligne.data} (f g : BD₂ ⟶ BD₁)
variables (h : homotopy f g)

variables (c_ c₁' c₂' : ℕ → ℝ≥0)
variables [BD.suitable c_] [BD₁.suitable c₁'] [BD₂.suitable c₂']
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0)

section homotopy

variables (M : (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ)

open differential_object differential_object.complex_like

def BD_map₂ (a₁ a₂ b₁ b₂ : ℕ → ℝ≥0)
  [∀ (i : ℕ), fact (b₁ i ≤ r' * a₁ i)] [∀ (i : ℕ), fact (b₂ i ≤ r' * a₂ i)]
  [BD₁.suitable a₁] [BD₂.suitable a₂] [BD₁.suitable b₁] [BD₂.suitable b₂]
  [∀ i, (f.f i).suitable (a₂ i) (a₁ i)]
  [∀ i, (f.f i).suitable (b₂ i) (b₁ i)] :
  BD₁.complex₂ r V r' a₁ b₁ ⟶ BD₂.complex₂ r V r' a₂ b₂ :=
{ app := λ M,
  { f := λ i, ((f.f i).eval_CLCFPTinv₂ r V r' (a₁ i) (b₁ i) (a₂ i) (b₂ i)).app M,
    comm := begin
      intros i j,
      show ((BD₁.complex₂ r V r' a₁ b₁).obj M).d i j ≫ _ =
        _ ≫ ((BD₂.complex₂ r V r' a₂ b₂).obj M).d i j,
      dsimp [data.complex₂_obj_d, data.complex₂_d],
      have : BD₂.d j i ≫ f.f i = f.f j ≫ BD₁.d j i := f.comm j i,
      simp only [← nat_trans.comp_app, ← universal_map.eval_CLCFPTinv₂_comp r V r', this]
    end },
  naturality' := by { intros M₁ M₂ g, ext i : 2,
    exact ((f.f i).eval_CLCFPTinv₂ r V r' (a₁ i) (b₁ i) (a₂ i) (b₂ i)).naturality g,
    } }
.
def BD_map [∀ i, (f.f i).suitable (c₂' i) (c₁' i)] :
  BD₁.complex c₁' r V r' c ⟶ BD₂.complex c₂' r V r' c :=
BD_map₂ f r V _ _ _ _
.

variables {f g}

def homotopy₂ (a₁ a₂ b₁ b₂ : ℕ → ℝ≥0)
  [∀ (i : ℕ), fact (b₁ i ≤ r' * a₁ i)] [∀ (i : ℕ), fact (b₂ i ≤ r' * a₂ i)]
  [BD₁.suitable a₁] [BD₂.suitable a₂] [BD₁.suitable b₁] [BD₂.suitable b₂]
  [∀ i, (f.f i).suitable (a₂ i) (a₁ i)]
  [∀ i, (f.f i).suitable (b₂ i) (b₁ i)]
  [∀ i, (g.f i).suitable (a₂ i) (a₁ i)]
  [∀ i, (g.f i).suitable (b₂ i) (b₁ i)]
  [∀ j i, (h.h j i).suitable (a₂ j) (a₁ i)]
  [∀ j i, (h.h j i).suitable (b₂ j) (b₁ i)] :
  homotopy ((BD_map₂ f r V a₁ a₂ b₁ b₂).app M) ((BD_map₂ g r V a₁ a₂ b₁ b₂).app M) :=
{ h := λ j i, ((h.h i j).eval_CLCFPTinv₂ r V r' _ _ _ _).app M,
  h_eq_zero := λ i j hij,
  begin
    convert nat_trans.congr_app (universal_map.eval_CLCFPTinv₂_zero r V r' _ _ _ _) M,
    rw h.h_eq_zero,
    exact ne.symm hij
  end,
  comm :=
  begin
    simp only [htpy_idx_rel₁_tt_nat, htpy_idx_rel₂_tt_nat],
    rintro i j k rfl,
    simp only [nat.succ_ne_zero i, nat.succ_eq_add_one, false_and, or_false],
    rintro rfl,
    dsimp only [data.complex₂, data.complex₂_d],
    erw [← nat_trans.comp_app, ← nat_trans.comp_app],
    erw [← universal_map.eval_CLCFPTinv₂_comp r V r',
        ← universal_map.eval_CLCFPTinv₂_comp r V r'],
    rw [← nat_trans.app_add, ← universal_map.eval_CLCFPTinv₂_add],
    simp only [(add_comm _ _).trans (h.comm (i+1+1) (i+1) i
      (by simp only [htpy_idx_rel₁_ff_nat]; exact or.inl rfl)
      (by simp only [htpy_idx_rel₂_ff_nat]; exact or.inl rfl)),
      universal_map.eval_CLCFPTinv₂_sub],
    refl,
  end }

def homotopy [∀ i, (f.f i).suitable (c₂' i) (c₁' i)] [∀ i, (g.f i).suitable (c₂' i) (c₁' i)]
  [∀ j i, (h.h j i).suitable (c₂' j) (c₁' i)] :
  homotopy ((BD_map f c₁' c₂' r V c).app M) ((BD_map g c₁' c₂' r V c).app M) :=
homotopy₂ h r V M _ _ _ _

end homotopy

section rescale

variables (M : ProFiltPseuNormGrpWithTinv.{u} r')

-- warning: this might need `[fact (0 < N)]`
instance rescale_constants_suitable (N : ℝ≥0) :
  BD.suitable (rescale_constants c_ N) :=
by { delta rescale_constants, apply_instance }

variables (BD)

open opposite ProFiltPseuNormGrpWithTinv (of)

-- this is not `iso.refl` -- so close, and yet so far away
-- the difference is `M_{(c * c_i) * N⁻¹}` vs `M_{c * (c_i * N⁻¹)}`
theorem complex_rescale_eq (N : ℝ≥0) :
  (BD.complex (rescale_constants c_ N) r V r' c).obj (op M) =
  (BD.complex c_ r V r' c).obj (op $ of r' $ rescale N M) :=
begin
  dsimp only [data.complex, rescale_constants],
  haveI : ∀ c c_, fact (c * c_ * N⁻¹ ≤ c * (c_ * N⁻¹)) :=
    λ c c_, by simpa only [mul_assoc] using nnreal.fact_le_refl _,
  transitivity
    (BD.complex₂ r V r' (λ (i : ℕ), c * c_ i * N⁻¹) (λ (i : ℕ), r' * (c * c_ i) * N⁻¹)).obj (op $ of r' M),
  { simp only [mul_assoc, ProFiltPseuNormGrpWithTinv.of_coe] },
  refine cochain_complex.ext (λ i, _),
  dsimp only [data.complex₂, rescale_constants, data.complex₂_d],
  rw ← universal_map.eval_CLCFPTinv₂_rescale,
end

end rescale

section double

variables (BD) (M : ProFiltPseuNormGrpWithTinv.{u} r')

open ProFiltPseuNormGrpWithTinv (of)

open category_theory opposite

-- -- === !!! warning, the instance for `M × M` has sorry'd data
def double_iso_prod :
  (BD.double.complex c_ r V r' c).obj (op M) ≅
  (BD.complex c_ r V r' c).obj (op $ of r' $ M × M) :=
sorry

example (N : ℝ≥0) :
  (BD.double.complex (rescale_constants c_ N) r V r' c).obj (op M) ≅
  (BD.complex c_ r V r' c).obj (op $ of r' $ rescale N (M × M)) :=
(double_iso_prod BD _ r V c _) ≪≫ (eq_to_iso $ complex_rescale_eq _ _ _ _ _ _ _)

end double

end breen_deligne

namespace breen_deligne

universe variables v

variables (BD : breen_deligne.package)

variables (c_ c' : ℕ → ℝ≥0)
variables [BD.data.suitable c_]
variables (r : ℝ≥0) (V : NormedGroup.{v}) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0)
variables (M : (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ)
variables (k' : ℝ≥0) (N : ℕ) [fact (1 ≤ k')] [fact (k' ≤ 2 ^ N)]

def homotopy_σπ
  [BD.data.suitable (c' * c_)]
  [∀ (j i : ℕ), ((BD.data.homotopy_pow BD.homotopy N).h j i).suitable (rescale_constants c_ (2 ^ N) j) ((c' * c_) i)]
  [∀ (i : ℕ), ((data.hom_pow BD.data.σ N).f i).suitable (rescale_constants c_ (2 ^ N) i) ((c' * c_) i)]
  [∀ (i : ℕ), ((data.hom_pow BD.data.π N).f i).suitable (rescale_constants c_ (2 ^ N) i) ((c' * c_) i)]
 :=
homotopy.{u v} (data.homotopy_pow BD.data BD.homotopy N)
  (c' * c_) (rescale_constants c_ (2^N)) r V c M

end breen_deligne
