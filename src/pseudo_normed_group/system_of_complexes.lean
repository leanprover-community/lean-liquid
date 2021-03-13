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

section
variables (BD : breen_deligne.package) (c' : ℕ → ℝ≥0)
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0)

/-- The object for the complex of normed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex_X (i : ℕ) : NormedGroup := CLCFPTinv r V r' M (c * c' i) (BD.rank i)

variables [BD.suitable c']

/-- The differential for the complex of normed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex_d (i : ℕ) : BD.complex_X c' r V M c i ⟶ BD.complex_X c' r V M c (i+1) :=
(BD.map i).eval_CLCFPTinv r V r' M (c * c' (i+1)) (c * c' i)

lemma complex_d_comp_d (i : ℕ) :
  BD.complex_d c' r V M c i ≫ BD.complex_d c' r V M c (i+1) = 0 :=
begin
  dsimp only [complex_d, complex_X],
  rw [← (BD.map i).eval_CLCFPTinv_comp r V r' M _ (c * c' (i+1)) _ (BD.map (i+1))],
  simp only [BD.map_comp_map, universal_map.eval_CLCFPTinv_zero],
  apply_instance
end

end

variables (BD : breen_deligne.package) (c' : ℕ → ℝ≥0) [BD.suitable c']
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
variables {M M₁ M₂ M₃ : ProFiltPseuNormGrpWithTinv.{u} r'} (c : ℝ≥0)
variables (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)

/-- The complex of normed groups `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : ProFiltPseuNormGrpWithTinv r') (c : ℝ≥0) :
  cochain_complex ℕ NormedGroup :=
cochain_complex.mk'
  (BD.complex_X c' r V M c)
  (BD.complex_d c' r V M c)
  (BD.complex_d_comp_d c' r V M c)

namespace complex

/-- The induced map of complexes from a homomorphism `M₁ ⟶ M₂`. -/
@[simps]
def map : BD.complex c' r V r' M₂ c ⟶ BD.complex c' r V r' M₁ c :=
differential_object.hom.mk'
  (λ i, CLCFPTinv.map r V r' _ _ f)
  begin
    rintro i j h, dsimp only [differential_object.coherent_indices] at h, subst j,
    dsimp [complex], simp only [category.comp_id, if_congr, if_true, eq_self_iff_true],
    symmetry, apply universal_map.map_comp_eval_CLCFPTinv
  end

variables (M)

@[simp] lemma map_id : map BD c' r V r' c (𝟙 M) = 𝟙 (BD.complex c' r V r' M c) :=
by { ext i : 2, apply CLCFPTinv.map_id }

lemma map_comp : map BD c' r V r' c (f ≫ g) = map BD c' r V r' c g ≫ map BD c' r V r' c f :=
by { ext i : 2, apply CLCFPTinv.map_comp }

lemma map_norm_noninc (n : ℕ) : ((map BD c' r V r' c f).f n).norm_noninc :=
CLCFPTinv.map_norm_noninc _ _ _ _ _ _

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
    (λ i,
    by haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := h.unop.down.down;
      exact CLCFPTinv.res r V r' _ _ (BD.rank i))
    begin
      rintro i j h, dsimp only [differential_object.coherent_indices] at h, subst j,
      dsimp [complex], simp only [category.comp_id, if_congr, if_true, eq_self_iff_true],
      symmetry, apply universal_map.res_comp_eval_CLCFPTinv
    end,
  map_id' := /- the restriction map for `c ≤ c` is the identity -/
  by { intro c, ext i : 2, exact CLCFPTinv.res_refl r V r' _ _ },
  map_comp' := /- composition of transition maps is a transition map -/
  begin
    intros c₃ c₂ c₁ h h',
    haveI H' : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := h'.unop.down.down,
    haveI H : fact ((unop c₂ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := h.unop.down.down,
    haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := le_trans H' H,
    ext i : 2, symmetry, exact CLCFPTinv.res_comp_res r V r' _ _ _ _,
  end }
.

namespace system

/-- The induced map of systems of complexes from a homomorphism `M₁ ⟶ M₂`. -/
@[simps]
def map : BD.system c' r V r' M₂ ⟶ BD.system c' r V r' M₁ :=
{ app := λ c, complex.map BD c' r V r' (unop c) f,
  naturality' := λ M₁ M₂ f, by { ext i : 2, symmetry, apply CLCFPTinv.map_comp_res } }

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
