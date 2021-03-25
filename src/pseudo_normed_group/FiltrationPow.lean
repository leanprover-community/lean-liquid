import pseudo_normed_group.breen_deligne
import normed_group.NormedGroup

open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow

-- move this
def Profinite.of (X : Type*)
  [topological_space X] [t2_space X] [totally_disconnected_space X] [compact_space X] :
  Profinite :=
{ to_Top := Top.of X,
  is_compact := ‹_›,
  is_t2 := ‹_›,
  is_totally_disconnected := ‹_› }

@[simps]
def pseudo_normed_group.filtration_obj
  (M) [profinitely_filtered_pseudo_normed_group M] (c) : Profinite :=
Profinite.of (pseudo_normed_group.filtration M c)

@[simps]
def ProFiltPseuNormGrpWithTinv.level
  (c : ℝ≥0) : ProFiltPseuNormGrpWithTinv c ⥤ Profinite :=
{ obj := λ M, pseudo_normed_group.filtration_obj M c,
  map := λ M N f, ⟨f.level c, f.level_continuous c⟩ }

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group
open profinitely_filtered_pseudo_normed_group_with_Tinv

/-- The "functor" that sends `M` and `c` to `(filtration M c)^n` -/
@[simps]
def Pow (n : ℕ) : Profinite ⥤ Profinite :=
{ obj := λ A, of (A^n),
  map := λ A B f, {
    to_fun := λ x j, f (x j),
    continuous_to_fun :=
    begin
      -- factor this into a separate lemma `continuous.pi_map`?
      apply continuous_pi,
      intro j,
      exact f.2.comp (continuous_apply j),
    end } }

universe variable u
variables {r' : ℝ≥0} {M M₁ M₂ M₃ : Type u}
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₁]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₂]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₃]
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ) (ϕ : basic_universal_map m n)
variables (f : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂)
variables (g : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₂ M₃)

@[simps]
def profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv₀_hom
  (c c₂ : ℝ≥0) [fact (r'⁻¹ * c ≤ c₂)] : filtration_obj M c ⟶ filtration_obj M c₂ :=
by exact ⟨Tinv₀ c c₂, Tinv₀_continuous _ _⟩

open profinitely_filtered_pseudo_normed_group_with_Tinv

/-- The "functor" that sends `M` and `c` to `(filtration M c)^n` -/
def FiltrationPow (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  ProFiltPseuNormGrpWithTinv c ⥤ Profinite :=
ProFiltPseuNormGrpWithTinv.level c ⋙ Pow n

namespace FiltrationPow

@[simps]
def cast_le [fact (c₁ ≤ c₂)] : (FiltrationPow r' c₁ n).obj M ⟶ (FiltrationPow r' c₂ n).obj M :=
(Pow n).map ⟨cast_le, (embedding_cast_le c₁ c₂).continuous⟩

@[simp] lemma cast_le_refl : cast_le r' c c n = 𝟙 (FiltrationPow r' M c n) := by { ext, refl }

lemma cast_le_trans [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ c₃)] :
  cast_le r' c₁ c₂ n ≫ cast_le r' c₂ c₃ n = @cast_le r' M _ c₁ c₃ n _ :=
by { ext, refl }

lemma map_comp_cast_le [fact (c₁ ≤ c₂)] :
  map r' c₁ n f ≫ cast_le r' c₁ c₂ n = cast_le r' c₁ c₂ n ≫ map r' c₂ n f :=
by { ext, refl }

@[simps]
def Tinv : FiltrationPow r' M c n ⟶ FiltrationPow r' M (r'⁻¹ * c) n :=
(Pow n).map (Tinv₀_hom _ c (r'⁻¹ * c))

lemma map_comp_Tinv :
  map r' c n f ≫ Tinv r' c n = Tinv r' c n ≫ map r' (r'⁻¹ * c) n f :=
by { ext x j, exact (f.map_Tinv (x j).1).symm }

lemma cast_le_comp_Tinv [fact (c₁ ≤ c₂)] :
  cast_le r' c₁ c₂ n ≫ (@Tinv r' M _ c₂ n) =
    Tinv r' c₁ n ≫ cast_le r' (r'⁻¹ * c₁) (r'⁻¹ * c₂) n :=
by { ext, refl }

end FiltrationPow

namespace breen_deligne
namespace basic_universal_map

open FiltrationPow

variables (M) {l m n}

@[simps]
def eval_FP [ϕ.suitable c₁ c₂] : FiltrationPow r' M c₁ m ⟶ FiltrationPow r' M c₂ n :=
{ to_fun := ϕ.eval_png₀ M c₁ c₂,
  continuous_to_fun := ϕ.eval_png₀_continuous M c₁ c₂ }

lemma eval_FP_comp (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] [(g.comp f).suitable c₁ c₃] :
  (g.comp f).eval_FP r' M c₁ c₃ =
  f.eval_FP r' M c₁ c₂ ≫ g.eval_FP r' M c₂ c₃ :=
begin
  ext j s i,
  dsimp,
  simp only [eval_png₀, subtype.coe_mk],
  rw eval_png_comp,
  simp only [add_monoid_hom.coe_comp, function.comp_app],
  refl,
end

lemma map_comp_eval_FP [ϕ.suitable c₁ c₂] :
  map r' c₁ m f ≫ ϕ.eval_FP r' M₂ c₁ c₂ = ϕ.eval_FP r' M₁ c₁ c₂ ≫ map r' c₂ n f :=
begin
  ext1 x,
  show ϕ.eval_png₀ M₂ c₁ c₂ (map r' c₁ m f x) = map r' c₂ n f (ϕ.eval_png₀ M₁ c₁ c₂ x),
  ext j,
  dsimp only [basic_universal_map.eval_png₀],
  simp only [basic_universal_map.eval_png_apply, f.map_sum, map_to_fun, subtype.coe_mk,
    pow_incl_apply, f.level_coe],
  apply fintype.sum_congr,
  intro i,
  simp only [← gsmul_eq_smul],
  exact (f.to_add_monoid_hom.map_gsmul _ _).symm
end

lemma cast_le_comp_eval_FP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  cast_le r' c₁ c₂ m ≫ ϕ.eval_FP r' M c₂ c₄ = ϕ.eval_FP r' M c₁ c₃ ≫ cast_le r' c₃ c₄ n :=
by { ext, refl }

open profinitely_filtered_pseudo_normed_group_with_Tinv

lemma Tinv_comp_eval_FP [ϕ.suitable c₁ c₂] :
  Tinv r' c₁ m ≫ ϕ.eval_FP r' M (r'⁻¹ * c₁) (r'⁻¹ * c₂) =
    ϕ.eval_FP r' M c₁ c₂ ≫ Tinv r' c₂ n :=
begin
  ext1 x,
  show ϕ.eval_png₀ M (r'⁻¹ * c₁) (r'⁻¹ * c₂) (Tinv r' c₁ m x) =
    Tinv r' c₂ n (ϕ.eval_png₀ M c₁ c₂ x),
  ext j,
  dsimp only [eval_png₀],
  simp only [eval_png_apply, map_to_fun, subtype.coe_mk, pow_incl_apply,
    FiltrationPow.Tinv, Pow_map_to_fun, Tinv₀_hom_to_fun, Tinv₀_coe,
    profinitely_filtered_pseudo_normed_group_hom.map_sum],
  apply fintype.sum_congr,
  intro i,
  simp only [← gsmul_eq_smul],
  exact ((profinitely_filtered_pseudo_normed_group_hom.to_add_monoid_hom _).map_gsmul _ _).symm
end

end basic_universal_map
end breen_deligne

open breen_deligne
