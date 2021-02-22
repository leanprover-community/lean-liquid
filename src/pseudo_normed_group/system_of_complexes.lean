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
  cochain_complex NormedGroup :=
{ /- the objects -/
  X := int.extend_from_nat 0 $ λ i, CLCFPTinv r V r' M (c * c' i) (BD.rank i),
  /- the differentials -/
  d := int.extend_from_nat 0 $ λ i,
    (BD.map i).eval_CLCFPTinv r V r' M (c * c' (i+1)) (c * c' i),
  d_squared' := /- d^2 = 0 -/
  begin
    ext1 (i|i),
    { dsimp,
      simp only [pi.comp_apply, pi.zero_apply],
      rw ← universal_map.eval_CLCFPTinv_comp r V r' M
        _ (c * c' (i+1)) _ (BD.map i) (BD.map (i+1)),
      simp only [BD.map_comp_map, universal_map.eval_CLCFPTinv_zero],
      apply_instance },
    { show 0 ≫ _ = 0, rw [zero_comp] }
  end }

namespace complex

@[simp] lemma d_neg_succ_of_nat (n : ℕ) : (BD.complex c' r V r' M c).d -[1+n] = 0 := rfl

/-- The induced map of complexes from a homomorphism `M₁ ⟶ M₂`. -/
@[simps]
def map : BD.complex c' r V r' M₂ c ⟶ BD.complex c' r V r' M₁ c :=
{ f := int.extend_from_nat 0 $ λ i, CLCFPTinv.map r V r' _ _ f,
  comm' :=
  begin
    ext1 (i|i),
    { dsimp, symmetry, apply universal_map.map_comp_eval_CLCFPTinv },
    { show 0 ≫ _ = 0, rw [zero_comp] }
  end }

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
  { f := int.extend_from_nat 0 $ λ i,
    by { haveI : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₂ : ℝ≥0)) := h.unop.down.down,
      exact CLCFPTinv.res r V r' _ _ (BD.rank i) },
    comm' :=
    begin
      ext1 (i|i),
      { dsimp [int.extend_from_nat], symmetry, apply universal_map.res_comp_eval_CLCFPTinv },
      { dsimp [int.extend_from_nat, complex.d_neg_succ_of_nat], rw [zero_comp, comp_zero], }
    end },
  map_id' := /- the restriction map for `c ≤ c` is the identity -/
  begin
    intro c,
    ext (i|i) : 2,
    { dsimp [int.extend_from_nat], rw CLCFPTinv.res_refl r V r' _ _, },
    { dsimp [int.extend_from_nat], ext }
  end,
  map_comp' := /- composition of transition maps is a transition map -/
  begin
    intros c₃ c₂ c₁ h h',
    haveI H' : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₂ : ℝ≥0)) := h'.unop.down.down,
    haveI H : fact (((unop c₂ : ℝ≥0) : ℝ) ≤ (unop c₃ : ℝ≥0)) := h.unop.down.down,
    have : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₃ : ℝ≥0)) := le_trans H' H,
    ext (i|i) : 2,
    { dsimp [int.extend_from_nat], rw CLCFPTinv.res_comp_res r V r' _ _ _ _ },
    { dsimp [int.extend_from_nat], simp only [pi.zero_apply, zero_comp], },
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
    { dsimp [int.extend_from_nat], rw zero_comp },
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
