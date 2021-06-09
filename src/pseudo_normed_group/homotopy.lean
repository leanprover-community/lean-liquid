import algebra.homology.homotopy

import pseudo_normed_group.system_of_complexes
import rescale.Tinv

/-!

*TODO*: find someone who can explain what is going on in this file.

-/

noncomputable theory

universe variables u

open_locale nnreal

open category_theory homological_complex

namespace breen_deligne

variables {BD BD₁ BD₂ : breen_deligne.data} (f g : BD₂ ⟶ BD₁)
variables (h : homotopy f g)

variables (κ c_₁ c_₂ : ℕ → ℝ≥0)
variables [BD.suitable κ] [BD₁.suitable c_₁] [BD₂.suitable c_₂]
variables (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0)

section homotopy

variables (M : (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ)

open homological_complex

@[simps app_f]
def BD_map₂ (a₁ a₂ b₁ b₂ : ℕ → ℝ≥0)
  [∀ (i : ℕ), fact (b₁ i ≤ r' * a₁ i)] [∀ (i : ℕ), fact (b₂ i ≤ r' * a₂ i)]
  [BD₁.suitable a₁] [BD₂.suitable a₂] [BD₁.suitable b₁] [BD₂.suitable b₂]
  [∀ i, (f.f i).suitable (a₂ i) (a₁ i)]
  [∀ i, (f.f i).suitable (b₂ i) (b₁ i)] :
  BD₁.complex₂ r V r' a₁ b₁ ⟶ BD₂.complex₂ r V r' a₂ b₂ :=
{ app := λ M,
  { f := λ i, ((f.f i).eval_CLCFPTinv₂ r V r' (a₁ i) (b₁ i) (a₂ i) (b₂ i)).app M,
    comm' := begin
      intros i j _,
      dsimp [data.complex₂_obj_d, data.complex₂_d],
      have : f.f j ≫ BD₁.d j i = BD₂.d j i ≫ f.f i := f.comm j i,
      simp only [← nat_trans.comp_app, ← universal_map.eval_CLCFPTinv₂_comp r V r', this],
    end },
  naturality' := by { intros M₁ M₂ g, ext i : 2,
    exact ((f.f i).eval_CLCFPTinv₂ r V r' (a₁ i) (b₁ i) (a₂ i) (b₂ i)).naturality g, } }
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
      dsimp only [data.system_obj, BD_map, BD_map₂_app_f],
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

end homotopy

end breen_deligne
