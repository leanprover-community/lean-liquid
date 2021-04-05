import for_mathlib.extend_from_nat

import system_of_complexes.basic
import pseudo_normed_group.Tinv
import pseudo_normed_group.category
import for_mathlib.arrow

open_locale classical nnreal
noncomputable theory

open opposite pseudo_normed_group category_theory category_theory.limits breen_deligne


universe variable u

namespace breen_deligne
namespace data

section
variables (BD : breen_deligne.data) (c' : ℕ → ℝ≥0)
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0)

/-- The object for the complex of normed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex₂_X (a b : ℕ → ℝ≥0) [∀ i, fact (b i ≤ r' * a i)] (i : ℕ) :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ NormedGroup :=
CLCFPTinv₂ r V r' (a i) (b i) (BD.X i)

/-- The object for the complex of normed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex_X (i : ℕ) : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ NormedGroup :=
complex₂_X BD r V r' (λ i, c * c' i) (λ i, r' * (c * c' i)) i
-- CLCFPTinv r V r' (c * c' i) (BD.X i)

variables [BD.suitable c']

-- class suitable₂ (a b : ℕ → ℝ≥0) :=
-- (le : ∀ i j, universal_map.suitable (a i) (a j) (BD.d i j))

/-- The differential for the complex of normed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex₂_d (a b : ℕ → ℝ≥0) [∀ i, fact (b i ≤ r' * a i)]
  [BD.suitable a] [BD.suitable b] (i j : ℕ) :
  BD.complex₂_X r V r' a b i ⟶ BD.complex₂_X r V r' a b j :=
(BD.d j i).eval_CLCFPTinv₂ r V r' _ _ _ _

/-- The differential for the complex of normed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex_d (i j : ℕ) : BD.complex_X c' r V r' c i ⟶ BD.complex_X c' r V r' c j :=
(BD.d j i).eval_CLCFPTinv r V r' (c * c' i) (c * c' j)

lemma complex_d_comp_d (i j k : ℕ) :
  BD.complex_d c' r V r' c i j ≫ BD.complex_d c' r V r' c j k = 0 :=
by simp only [complex_d, ← universal_map.eval_CLCFPTinv_comp, BD.d_comp_d,
    universal_map.eval_CLCFPTinv_zero]

end

open differential_object

variables (BD : breen_deligne.data) (c' : ℕ → ℝ≥0) [BD.suitable c']
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
variables {M M₁ M₂ M₃ : ProFiltPseuNormGrpWithTinv.{u} r'} (c : ℝ≥0)
variables (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)

/-- The complex of normed groups `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
@[simps]
def complex₂ (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
   (a b : ℕ → ℝ≥0) [∀ i, fact (b i ≤ r' * a i)] [BD.suitable a] [BD.suitable b] :
  (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ ⥤ cochain_complex ℕ NormedGroup :=
{ obj := λ M,
  { X := λ i, (BD.complex₂_X r V r' a b i).obj M,
    d := λ i j, (BD.complex₂_d r V r' a b i j).app M,
    d_comp_d := λ i j k,
    begin
      rw [← nat_trans.comp_app],
      simp only [complex₂_d, ← universal_map.eval_CLCFPTinv₂_comp, BD.d_comp_d,
        universal_map.eval_CLCFPTinv₂_zero],
      refl
    end,
    d_eq_zero := λ i j hij,
    begin
      have : ¬ differential_object.coherent_indices ff j i := ne.symm hij,
      simp only [complex₂_d, ← universal_map.eval_CLCFPTinv₂_comp, BD.d_eq_zero this,
        universal_map.eval_CLCFPTinv₂_zero],
      refl
    end },
  map := λ M₁ M₂ f,
  { f := λ i, ((CLCFPTinv₂ r V r' (a i) (b i) (BD.X i)).map f : _),
    comm := λ i j, (nat_trans.naturality _ _).symm },
  map_id' := λ M, by { ext i : 2, apply category_theory.functor.map_id, },
  map_comp' := λ M₁ M₂ M₃ f g, by { ext i : 2, apply category_theory.functor.map_comp } }

/-- The complex of normed groups `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0) :
  (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ ⥤ cochain_complex ℕ NormedGroup :=
BD.complex₂ r V r' (λ i, c * c' i) (λ i, r' * (c * c' i))

namespace complex

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) (n : ℕ) :
  (((BD.complex c' r V r' c).map f).f n).norm_noninc :=
CLCFPTinv.map_norm_noninc _ _ _ _ _ _

end complex

theorem comm_sq_app {C D} [category C] [category D]
  {X₁ X₂ Y₁ Y₂ : C ⥤ D} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {φ : X₁ ⟶ X₂} {ψ : Y₁ ⟶ Y₂}
  (hf : f₁ ≫ ψ = φ ≫ f₂) (c : C) : f₁.app c ≫ ψ.app c = φ.app c ≫ f₂.app c :=
by rw [← nat_trans.comp_app, ← nat_trans.comp_app, hf]

/-- The system of complexes
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ ...`
occurring in Theorems 9.4 and 9.5 of [Analytic], as a functor in `M`. -/
-- @[simps]
def system (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ system_of_complexes :=
functor.flip {
  obj := λ c, BD.complex c' r V r' (unop c),
  map := λ c₂ c₁ h,
    { app := λ M, begin
        haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h.unop.down.down⟩,
        refine differential_object.hom.mk' (λ i, _) _,
        { exact (CLCFPTinv₂.res r V r' _ _ _ _ (BD.X i)).app _ },
        { intros i j hij, apply comm_sq_app,
          symmetry, apply universal_map.res_comp_eval_CLCFPTinv₂ },
      end,
      naturality' := λ M N f, begin
        ext i : 2,
        erw [comp_f, comp_f],
        apply nat_trans.naturality,
      end },
  map_id' := by {
    intro c, ext M i : 4,
    refine nat_trans.congr_app (CLCFPTinv₂.res_refl r V r' _ _ _) M },
  map_comp' := begin
    intros c₃ c₂ c₁ h h',
    haveI H' : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h'.unop.down.down⟩,
    haveI H : fact ((unop c₂ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := ⟨h.unop.down.down⟩,
    haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := ⟨H'.out.trans H.out⟩,
    ext M i : 4, symmetry,
    exact nat_trans.congr_app (CLCFPTinv₂.res_comp_res r V r' _ _ _ _ _ _ _) _,
  end }

end data

end breen_deligne

#lint- only unused_arguments def_lemma doc_blame
