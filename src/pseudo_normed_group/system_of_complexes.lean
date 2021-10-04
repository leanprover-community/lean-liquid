import system_of_complexes.basic
import pseudo_normed_group.Tinv
import pseudo_normed_group.category

/-!

# The system of complexes in Theorem 9.4 of `analytic.pdf`

Theorem 9.4 is about a system of complexes built from Breen-Deligne data,
a seminormed group `V` with `T⁻¹` (scaling by `r`) and a (certain explicit) profinitely filtered
pseudo-normed group `M` with `T⁻¹` (scaling by `r'`). We do not specialise to Scholze's
`𝓜-bar_r'(S)` in this file, but allow general profinitely filtered `M`. This file
contains the construction of the system of complexes from this data.

## Main definitions

Let `BD = (n₁ ⟶ n₂ ⟶ …)` be Breen-Deligne data, `κ` a sequence of non-negative reals which are
suitable for `BD`, and say `r,c≥0` and `V` is a normed group with `T⁻¹` scaling by `r`.

- `BD.complex κ r V r' c`: the functor taking a profinitely filtered pseudo-normed group `M`
  to the cochain complex `V-hat(M_{≤c}^n₁)^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^n₂)^{T⁻¹} ⟶ …`
  induced by the data.

- `BD.system κ r V r'`: the functor sending a profinitely filtered pseudo-normed group `M`
  to the system of complexes whose component at `c`
  is `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …`

-/
open_locale classical nnreal
noncomputable theory

open opposite pseudo_normed_group category_theory category_theory.limits breen_deligne


universe variable u

namespace breen_deligne
namespace data

section
variables (BD : breen_deligne.data) (κ : ℕ → ℝ≥0)
variables (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (r' ≤ 1)]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0)

/-- The object for the complex of seminormed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex₂_X (a b : ℕ → ℝ≥0) [∀ i, fact (b i ≤ r' * a i)] (i : ℕ) :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup :=
CLCFPTinv₂ r V r' (a i) (b i) (BD.X i)
/-- The object for the complex of seminormed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex_X (i : ℕ) : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup :=
complex₂_X BD r V r' (λ i, c * κ i) (λ i, r' * (c * κ i)) i

variable [fact (0 < r')]
variables [BD.suitable κ]

/-- The differential for the complex of seminormed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex₂_d (a b : ℕ → ℝ≥0) [∀ i, fact (b i ≤ r' * a i)]
  [BD.suitable a] [BD.suitable b] (i j : ℕ) :
  BD.complex₂_X r V r' a b i ⟶ BD.complex₂_X r V r' a b j :=
(BD.d j i).eval_CLCFPTinv₂ r V r' _ _ _ _

/-- The differential for the complex of seminormed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex_d (i j : ℕ) : BD.complex_X κ r V r' c i ⟶ BD.complex_X κ r V r' c j :=
(BD.d j i).eval_CLCFPTinv r V r' (c * κ i) (c * κ j)

lemma complex_d_comp_d (i j k : ℕ) :
  BD.complex_d κ r V r' c i j ≫ BD.complex_d κ r V r' c j k = 0 :=
by simp only [complex_d, ← universal_map.eval_CLCFPTinv_comp, BD.d_comp_d,
    universal_map.eval_CLCFPTinv_zero]

end

section

open homological_complex

variables (BD : breen_deligne.data) (κ : ℕ → ℝ≥0) [BD.suitable κ]
variables (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0)

/-- The complex of seminormed groups `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
@[simps]
def complex₂ (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
   (a b : ℕ → ℝ≥0) [∀ i, fact (b i ≤ r' * a i)] [BD.suitable a] [BD.suitable b] :
  (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ ⥤ cochain_complex SemiNormedGroup ℕ :=
{ obj := λ M,
  { X := λ i, (BD.complex₂_X r V r' a b i).obj M,
    d := λ i j, (BD.complex₂_d r V r' a b i j).app M,
    d_comp_d' := λ i j k _ _,
    begin
      rw [← nat_trans.comp_app],
      simp only [complex₂_d, ← universal_map.eval_CLCFPTinv₂_comp, BD.d_comp_d,
        universal_map.eval_CLCFPTinv₂_zero],
      refl
    end,
    shape' := λ i j hij,
    begin
      simp only [complex₂_d, ← universal_map.eval_CLCFPTinv₂_comp, BD.shape _ _ hij,
        universal_map.eval_CLCFPTinv₂_zero],
      refl
    end },
  map := λ M₁ M₂ f,
  { f := λ i, ((CLCFPTinv₂ r V r' (a i) (b i) (BD.X i)).map f : _),
    comm' := λ i j _, nat_trans.naturality _ _ },
  map_id' := λ M, by { ext i : 2, apply category_theory.functor.map_id, },
  map_comp' := λ M₁ M₂ M₃ f g, by { ext i : 2, apply category_theory.functor.map_comp } }

/-- The complex of seminormed groups `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0) :
  (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ ⥤ cochain_complex SemiNormedGroup ℕ :=
BD.complex₂ r V r' (λ i, c * κ i) (λ i, r' * (c * κ i))

namespace complex

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) (n : ℕ) :
  (((BD.complex κ r V r' c).map f).f n).norm_noninc :=
CLCFPTinv.map_norm_noninc _ _ _ _ _ _

end complex

lemma complex_obj_d (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0) (i j : ℕ) (M) :
  ((BD.complex κ r V r' c).obj M).d i j =
    ((BD.d j i).eval_CLCFPTinv r V r' _ _).app M :=
rfl

theorem comm_sq_app {C D} [category C] [category D]
  {X₁ X₂ Y₁ Y₂ : C ⥤ D} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {φ : X₁ ⟶ X₂} {ψ : Y₁ ⟶ Y₂}
  (hf : f₁ ≫ ψ = φ ≫ f₂) (c : C) : f₁.app c ≫ ψ.app c = φ.app c ≫ f₂.app c :=
by rw [← nat_trans.comp_app, ← nat_trans.comp_app, hf]

/-- The system of complexes
`V-hat(M_{≤c}^{n₁})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^{n₂})^{T⁻¹} ⟶ ...`
occurring in Theorems 9.4 and 9.5 of [Analytic], as a functor in `M`. -/
@[simps obj map]
def system (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ system_of_complexes :=
functor.flip {
  obj := λ c, BD.complex κ r V r' (unop c),
  map := λ c₂ c₁ h,
    { app := λ M, begin
        haveI : fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h.unop.down.down⟩,
        refine
        { f := λ i, (CLCFPTinv₂.res r V r' _ _ _ _ (BD.X i)).app _,
          comm' := _ },
        { intros i j _, apply comm_sq_app,
          apply universal_map.res_comp_eval_CLCFPTinv₂ },
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
.

-- move this
instance fact_unop_op {c₁ c₂ : ℝ≥0} [fact (c₂ ≤ c₁)] :
  fact ((unop (op c₂)) ≤ (unop (op c₁))) :=
by { dsimp, apply_assumption }

lemma system_res_def (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] {M}
  {c₁ c₂ : ℝ≥0} {i : ℕ} [h : fact (c₂ ≤ c₁)] :
  @system_of_complexes.res ((BD.system κ r V r').obj M) c₁ c₂ i _ =
    (CLCFPTinv.res r V r' _ _ _).app M :=
rfl

lemma system_obj_d (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
  (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] {M}
  (c : ℝ≥0) (i j : ℕ) :
  @system_of_complexes.d ((BD.system κ r V r').obj M) c i j =
    ((BD.d j i).eval_CLCFPTinv r V r' _ _).app M :=
rfl

lemma system_map_iso_isometry {M₁ M₂ : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ}
  (f : M₁ ≅ M₂) (i : ℕ) :
  isometry ((((BD.system κ r V r').map_iso f).hom.app (op c)).f i) :=
begin
  simp only [← iso.app_hom, ← homological_complex.hom.iso_app_hom],
  apply SemiNormedGroup.iso_isometry_of_norm_noninc;
  apply complex.map_norm_noninc,
end

instance system.separated_space (c : ℝ≥0) (i : ℕ) (M) :
  separated_space (((BD.system κ r V r').obj M) c i) :=
CLCFPTinv₂.separated_space _ _ _ _ _ _ _

instance system.complete_space (c : ℝ≥0) (i : ℕ) (M) :
  complete_space (((BD.system κ r V r').obj M) c i) :=
CLCFPTinv₂.complete_space _ _ _ _ _ _ _

end

section

variables (BD : breen_deligne.data)
variables (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
variables (κ : ℕ → ℝ≥0) [BD.very_suitable r r' κ]

variables {r V r' κ}

lemma system_admissible {M} : ((BD.system κ r V r').obj M).admissible :=
{ d_norm_noninc' := λ c i j hij,
  begin
    haveI : universal_map.very_suitable (BD.d j i) r r' (unop (op c) * κ j) (unop (op c) * κ i) :=
    by { dsimp only [unop_op], apply_instance },
    exact universal_map.eval_CLCFPTinv_norm_noninc _ _ _ _ _ _ _,
  end,
  res_norm_noninc := λ c₁ c₂ i h, CLCFPTinv.res_norm_noninc _ _ _ _ _ _ _, }

end

end data

end breen_deligne

#lint- only unused_arguments def_lemma doc_blame
