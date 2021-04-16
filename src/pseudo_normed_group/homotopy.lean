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

variables (c_ c_₁ c_₂ : ℕ → ℝ≥0)
variables [BD.suitable c_] [BD₁.suitable c_₁] [BD₂.suitable c_₂]
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0)

section homotopy

variables (M : (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ)

open differential_object differential_object.complex_like

@[simps app_f]
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

@[simps app_f]
def BD_map [∀ i, (f.f i).suitable (c_₂ i) (c_₁ i)] :
  BD₁.complex c_₁ r V r' c ⟶ BD₂.complex c_₂ r V r' c :=
BD_map₂ f r V _ _ _ _
.

-- @[simp] lemma BD_map_app_f [∀ i, (f.f i).suitable (c_₂ i) (c_₁ i)] (i : ℕ)
--   (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :
--   ((BD_map f c_₁ c_₂ r V c).app M).f i =
--     ((f.f i).eval_CLCFPTinv r V r' (c_₁ i) (c_₂ i)).app M := _

open opposite

@[simps app_app]
def BD_system_map [∀ i, (f.f i).suitable (c_₂ i) (c_₁ i)] :
  BD₁.system c_₁ r V r' ⟶ BD₂.system c_₂ r V r' :=
{ app := λ M,
  { app := λ c, (BD_map f c_₁ c_₂ r V c.unop).app M,
    naturality' := λ x y hxy,
    begin
      ext i : 2,
      erw [comp_f, comp_f],
      dsimp only [data.system_obj, BD_map, BD_map₂_app_f, hom.mk'_f],
      haveI : fact (y.unop ≤ x.unop) := ⟨le_of_hom hxy.unop⟩,
      exact nat_trans.congr_app
        (universal_map.res_comp_eval_CLCFPTinv₂ r V r' _ _ _ _ _ _ _ _ _) M,
    end },
  naturality' := λ M₁ M₂ g,
  begin
    ext c : 2,
    exact (BD_map f c_₁ c_₂ r V c.unop).naturality _
  end }
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
    rintro i j k hij hjk,
    dsimp only [data.complex₂, data.complex₂_d],
    erw [← nat_trans.comp_app, ← nat_trans.comp_app],
    erw [← universal_map.eval_CLCFPTinv₂_comp r V r',
        ← universal_map.eval_CLCFPTinv₂_comp r V r'],
    rw [← nat_trans.app_add, ← universal_map.eval_CLCFPTinv₂_add],
    rw eq_comm at hij hjk,
    rw and_comm at hij,
    simp only [(add_comm _ _).trans (h.comm k j i
      (by simp only [htpy_idx_rel₁_ff_nat]; exact hjk)
      (by simp only [htpy_idx_rel₂_ff_nat]; exact hij)),
      universal_map.eval_CLCFPTinv₂_sub],
    refl,
  end }

def homotopy [∀ i, (f.f i).suitable (c_₂ i) (c_₁ i)] [∀ i, (g.f i).suitable (c_₂ i) (c_₁ i)]
  [∀ j i, (h.h j i).suitable (c_₂ j) (c_₁ i)] :
  homotopy ((BD_map f c_₁ c_₂ r V c).app M) ((BD_map g c_₁ c_₂ r V c).app M) :=
homotopy₂ h r V M _ _ _ _

end homotopy

section rescale

variables (M : ProFiltPseuNormGrpWithTinv.{u} r')

-- move this
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

end breen_deligne

namespace breen_deligne

universe variables v

variables (BD : breen_deligne.package)
variables (c_ c' : ℕ → ℝ≥0)
variables [BD.data.suitable c_] [package.adept BD c_ c']
variables (r : ℝ≥0) (V : NormedGroup.{v}) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0)
variables (M : (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ)
variables (N : ℕ)

def homotopy_σπ :=
homotopy.{u v} (data.homotopy_mul BD.data BD.homotopy N)
  (c' * c_) (rescale_constants c_ (2^N)) r V c M

end breen_deligne
