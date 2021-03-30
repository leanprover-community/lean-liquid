import for_mathlib.extend_from_nat

import system_of_complexes.basic
import pseudo_normed_group.Tinv
import pseudo_normed_group.category

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
def complex_X (i : ℕ) : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ NormedGroup :=
CLCFPTinv r V r' (c * c' i) (BD.X i)

-- CLCFPTinv' r V n
--   (op (Profinite.of (filtration M c)))
--   (op (Profinite.of (filtration M (r' * c))))
--   (has_hom.hom.op ⟨
--       profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv₀' (r' * c) c,
--       profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv₀'_continuous (r' * c) c⟩)
--   (has_hom.hom.op ⟨cast_le, (embedding_cast_le _ _).continuous⟩)

-- theorem complex_X_hom_of_eq' (c₂' : ℕ → ℝ≥0) (i : ℕ) (h : c * c' i = c₂ * c₂' i) :

variables [BD.suitable c']

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
def complex (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0) :
  cochain_complex ℕ NormedGroup :=
{ X := λ i, (BD.complex_X c' r V r' c i).obj (op M),
  d := λ i j, (BD.complex_d c' r V r' c i j).app (op M),
  d_comp_d := λ i j k, by { rw ← nat_trans.comp_app _ _ (op M), rw complex_d_comp_d, refl },
  d_eq_zero := λ i j hij,
  begin
    have : ¬ differential_object.coherent_indices ff j i := ne.symm hij,
    simp only [complex_d, ← universal_map.eval_CLCFPTinv_comp, BD.d_eq_zero this,
      universal_map.eval_CLCFPTinv_zero],
    refl
  end }

namespace complex

/-- The induced map of complexes from a homomorphism `M₁ ⟶ M₂`. -/
-- @[simps] -- this is slow :sad:
def map : BD.complex c' r V r' M₂ c ⟶ BD.complex c' r V r' M₁ c :=
differential_object.hom.mk'
  (λ i, (CLCFPTinv r V r' _ _).map f.op) $ λ _ _ _, (nat_trans.naturality _ _).symm

variables (M)

@[simp] lemma map_id : map BD c' r V r' c (𝟙 M) = 𝟙 (BD.complex c' r V r' M c) :=
by { ext i : 2, apply category_theory.functor.map_id, }

lemma map_comp : map BD c' r V r' c (f ≫ g) = map BD c' r V r' c g ≫ map BD c' r V r' c f :=
by { ext i : 2, dsimp [map], apply category_theory.functor.map_comp }

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
    by haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h.unop.down.down⟩;
      exact (CLCFPTinv.res r V r' _ _ (BD.X i)).app _)
    begin
      rintro i j hij,
      dsimp [complex, complex_d],
      simp only [← nat_trans.comp_app],
      haveI H : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h.unop.down.down⟩,
      rw universal_map.res_comp_eval_CLCFPTinv r V r'
        (unop c₂ * c' i) (unop c₁ * c' i) (unop c₂ * c' j) (unop c₁ * c' j) (BD.d j i)
    end,
  map_id' := /- the restriction map for `c ≤ c` is the identity -/
  by { intro c, ext i : 2, dsimp, rw CLCFPTinv.res_refl r V r' _ _, refl },
  map_comp' := /- composition of transition maps is a transition map -/
  begin
    intros c₃ c₂ c₁ h h',
    haveI H' : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h'.unop.down.down⟩,
    haveI H : fact ((unop c₂ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := ⟨h.unop.down.down⟩,
    haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := ⟨H'.out.trans H.out⟩,
    ext i : 2, symmetry,
    exact nat_trans.congr_app (CLCFPTinv.res_comp_res r V r' _ _ _ _) _,
  end }
.

namespace system

/-- The induced map of systems of complexes from a homomorphism `M₁ ⟶ M₂`. -/
@[simps]
def map : BD.system c' r V r' M₂ ⟶ BD.system c' r V r' M₁ :=
{ app := λ c, complex.map BD c' r V r' (unop c) f,
  naturality' := λ M₁ M₂ f,
    by { ext i : 2, symmetry, apply (CLCFPTinv.res _ _ _ _ _ _).naturality _ } }

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

end data

end breen_deligne

#lint- only unused_arguments def_lemma doc_blame
