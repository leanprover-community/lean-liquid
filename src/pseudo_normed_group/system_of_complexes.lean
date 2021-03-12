import for_mathlib.extend_from_nat

import system_of_complexes.basic
import pseudo_normed_group.Tinv
import pseudo_normed_group.category

open_locale classical nnreal
noncomputable theory

open opposite pseudo_normed_group category_theory category_theory.limits breen_deligne


universe variable u

namespace breen_deligne
namespace package

variables (BD : breen_deligne.package) (c' : ℕ → ℝ≥0) [BD.suitable c']
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
variables {M M₁ M₂ M₃ : ProFiltPseuNormGrpWithTinv.{u} r'} (c : ℝ≥0)
variables (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)

/-- The complex of (uncompleted) normed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
@[simps]
def complex (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : ProFiltPseuNormGrpWithTinv r')
  (c : ℝ≥0) :
  cochain_complex ℤ NormedGroup :=
cochain_complex.mk'
  /- the objects -/
  (int.extend_from_nat 0 $ λ i, CLCFPTinv r V r' M (c * c' i) (BD.rank i))
  /- the differentials -/
  (int.extend_from_nat 0 $ λ i, (BD.map i).eval_CLCFPTinv r V r' M (c * c' (i+1)) (c * c' i))
  /- d^2 = 0 -/
  begin
    rintros (i|i),
    { show (BD.map i).eval_CLCFPTinv _ _ _ _ _ _ ≫ (BD.map (i+1)).eval_CLCFPTinv _ _ _ _ _ _ = 0,
      rw [← (BD.map i).eval_CLCFPTinv_comp r V r' M _ (c * c' (i+1)) _ (BD.map (i+1))],
      simp only [BD.map_comp_map, universal_map.eval_CLCFPTinv_zero],
      apply_instance },
    { show 0 ≫ _ = 0, rw [zero_comp] }
  end

namespace complex

/-- The induced map of complexes from a homomorphism `M₁ ⟶ M₂`. -/
@[simps]
def map : BD.complex c' r V r' M₂ c ⟶ BD.complex c' r V r' M₁ c :=
differential_object.hom.mk'
  (int.extend_from_nat 0 $ λ i, CLCFPTinv.map r V r' _ _ f)
  begin
    rintro (i|i) j h; dsimp only [differential_object.coherent_indices] at h; subst j,
    { dsimp, simp only [category.comp_id, if_congr, if_true, eq_self_iff_true],
      symmetry, apply universal_map.map_comp_eval_CLCFPTinv },
    { dsimp, simp only [category.comp_id, if_congr, if_true, eq_self_iff_true],
      show 0 ≫ _ = 0, rw [zero_comp] }
  end

variables (M)

@[simp] lemma map_id : map BD c' r V r' c (𝟙 M) = 𝟙 (BD.complex c' r V r' M c) :=
begin
  ext (i|i) : 2,
  { apply CLCFPTinv.map_id },
  { dsimp [int.extend_from_nat], ext, },
end

lemma map_comp : map BD c' r V r' c (f ≫ g) = map BD c' r V r' c g ≫ map BD c' r V r' c f :=
begin
  ext (i|i) : 2,
  { apply CLCFPTinv.map_comp },
  { dsimp [int.extend_from_nat], ext, },
end

lemma map_norm_noninc (n : ℤ) : ((map BD c' r V r' c f).f n).norm_noninc :=
begin
  rcases n with (n|n),
  { exact CLCFPTinv.map_norm_noninc _ _ _ _ _ _ },
  { intro v, exact norm_zero.le.trans (norm_nonneg _) }
end

end complex

/-- The system of complexes
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ ...`
occurring in Theorems 9.4 and 9.5 of [Analytic]. -/
@[simps]
def system (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : ProFiltPseuNormGrpWithTinv r') :
  system_of_complexes :=
{ /- the objects, aka the constituent complexes -/
  obj := λ c, BD.complex c' r V r' M (unop c : ℝ≥0),
  /- the restriction maps -/
  map := λ c₂ c₁ h,
  differential_object.hom.mk'
    (int.extend_from_nat 0 $ λ i,
    by haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := h.unop.down.down;
      exact CLCFPTinv.res r V r' _ _ (BD.rank i))
    begin
      rintro (i|i) j h; dsimp only [differential_object.coherent_indices] at h; subst j,
      { dsimp, simp only [category.comp_id, if_congr, if_true, eq_self_iff_true],
        symmetry, apply universal_map.res_comp_eval_CLCFPTinv },
      { dsimp, simp only [category.comp_id, if_congr, if_true, eq_self_iff_true],
        erw [zero_comp, comp_zero] }
    end,
  map_id' := /- the restriction map for `c ≤ c` is the identity -/
  begin
    intro c,
    ext (i|i) : 2,
    { exact CLCFPTinv.res_refl r V r' _ _, },
    { ext }
  end,
  map_comp' := /- composition of transition maps is a transition map -/
  begin
    intros c₃ c₂ c₁ h h',
    haveI H' : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := h'.unop.down.down,
    haveI H : fact ((unop c₂ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := h.unop.down.down,
    haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := le_trans H' H,
    ext (i|i) : 2,
    { symmetry, exact CLCFPTinv.res_comp_res r V r' _ _ _ _ },
    { show 0 = 0 ≫ _, rw [zero_comp], },
  end }
.

namespace system

/-- The induced map of systems of complexes from a homomorphism `M₁ ⟶ M₂`. -/
@[simps]
def map : BD.system c' r V r' M₂ ⟶ BD.system c' r V r' M₁ :=
{ app := λ c, complex.map BD c' r V r' (unop c) f,
  naturality' := λ M₁ M₂ f,
  begin
    ext (i|i) : 2,
    { dsimp, symmetry, apply CLCFPTinv.map_comp_res },
    { dsimp [int.extend_from_nat], show 0 ≫ _ = 0, rw zero_comp },
  end }

@[simp] lemma map_id : map BD c' r V r' (𝟙 M) = 𝟙 (BD.system c' r V r' M) :=
by { ext c : 2, apply complex.map_id }

lemma map_comp : map BD c' r V r' (f ≫ g) = map BD c' r V r' g ≫ map BD c' r V r' f :=
by { ext c : 2, apply complex.map_comp }

end system

/-- The system of complexes
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ ...`
as a functor in `M`.

See also `system`. -/
@[simps]
def System (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ system_of_complexes :=
{ obj := λ M, BD.system c' r V r' (unop M),
  map := λ M₁ M₂ f, system.map BD c' r V r' f.unop,
  map_id' := λ M, by apply system.map_id,
  map_comp' := λ M₁ M₂ M₃ f g, by apply system.map_comp }

end package
end breen_deligne

#lint- only unused_arguments def_lemma doc_blame
