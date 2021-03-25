import pseudo_normed_group.breen_deligne
import normed_group.NormedGroup

open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow
universe u

universe variable u

set_option pp.universes true

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
  (r' c : ℝ≥0) : ProFiltPseuNormGrpWithTinv.{u} r' ⥤ Profinite.{u} :=
{ obj := λ M, pseudo_normed_group.filtration_obj M c,
  map := λ M N f, ⟨f.level c, f.level_continuous c⟩ }

open profinitely_filtered_pseudo_normed_group category_theory

@[simps]
def Filtration (r' : ℝ≥0) : ProFiltPseuNormGrpWithTinv.{u} r' ⥤ (ℝ≥0 ⥤ Profinite.{u}) :=
{ obj := λ M,
  { obj := λ c, Profinite.of (pseudo_normed_group.filtration M c),
    map := λ c₁ c₂ h, ⟨_, @continuous_cast_le M _ c₁ c₂ ⟨le_of_hom h⟩⟩ },
  map := λ M₁ M₂ f,
  { app := λ c, ⟨f.level c, f.level_continuous c⟩ },
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group
open profinitely_filtered_pseudo_normed_group_with_Tinv

/-- The functor that sends `A` to `A^n` -/
@[simps]
def Pow (n : ℕ) : Profinite ⥤ Profinite :=
{ obj := λ A, of (A^n),
  map := λ A B f, {
    to_fun := λ x j, f (x j),
    continuous_to_fun := continuous_pi $ λ j, f.2.comp (continuous_apply j) } }

@[simps]
def profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv₀_hom
  {r' : ℝ≥0} (M : Type*) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]
  (c c₂ : ℝ≥0) [fact (r'⁻¹ * c ≤ c₂)] : filtration_obj M c ⟶ filtration_obj M c₂ :=
by exact ⟨Tinv₀ c c₂, Tinv₀_continuous _ _⟩

open profinitely_filtered_pseudo_normed_group_with_Tinv

/-- The "functor" that sends `M` and `c` to `(filtration M c)^n` -/
@[simps] def FiltrationPow (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  ProFiltPseuNormGrpWithTinv r' ⥤ Profinite :=
ProFiltPseuNormGrpWithTinv.level r' c ⋙ Pow n

namespace FiltrationPow

@[simps]
def cast_le (r' c₁ c₂ : ℝ≥0) [fact (c₁ ≤ c₂)] (n : ℕ) :
  FiltrationPow.{u} r' c₁ n ⟶ FiltrationPow r' c₂ n :=
{ app := λ M, (Pow n).map ⟨cast_le, (embedding_cast_le c₁ c₂).continuous⟩,
  naturality' := λ M N f, by { ext, refl } }

theorem cast_le_refl (r' c : ℝ≥0) (n : ℕ) : cast_le r' c c n = 𝟙 _ :=
by { ext, refl }

theorem cast_le_comp (r' c₁ c₂ c₃ : ℝ≥0) [h₁ : fact (c₁ ≤ c₂)] [h₂ : fact (c₂ ≤ c₃)] (n : ℕ) :
  cast_le r' c₁ c₂ n ≫ cast_le r' c₂ c₃ n =
  @cast_le r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n :=
by { ext, refl }

@[simps]
def Tinv (r' : ℝ≥0) (c c₂) [fact (r'⁻¹ * c ≤ c₂)] (n) :
  FiltrationPow r' c n ⟶ FiltrationPow r' c₂ n :=
{ app := λ M, (Pow n).map (Tinv₀_hom M c c₂),
  naturality' := λ M N f, by { ext x j, exact (f.map_Tinv (x j).1).symm } }

lemma cast_le_vcomp_Tinv (r' c₁ c₂ c₃ : ℝ≥0)
  [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (r'⁻¹ * c₁ ≤ c₂)] [fact (r'⁻¹ * c₂ ≤ c₃)] (n : ℕ) :
  cast_le r' c₁ c₂ n ≫ Tinv r' c₂ c₃ n = Tinv r' c₁ c₂ n ≫ cast_le r' c₂ c₃ n :=
by { ext, refl }

end FiltrationPow

namespace breen_deligne
namespace basic_universal_map

variables (r' c c₁ c₂ c₃ c₄ : ℝ≥0) {l m n : ℕ} (ϕ : basic_universal_map m n)

open FiltrationPow

@[simps]
def eval_FP [ϕ.suitable c₁ c₂] : FiltrationPow r' c₁ m ⟶ FiltrationPow r' c₂ n :=
{ app := λ M,
  { to_fun := ϕ.eval_png₀ M c₁ c₂,
    continuous_to_fun := ϕ.eval_png₀_continuous M c₁ c₂ },
  naturality' := λ M₁ M₂ f, begin
    ext1 x,
    change ϕ.eval_png₀ M₂ c₁ c₂ ((FiltrationPow r' c₁ m).map f x) =
      (FiltrationPow r' c₂ n).map f (ϕ.eval_png₀ M₁ c₁ c₂ x),
    ext j,
    dsimp only [basic_universal_map.eval_png₀],
    simp only [basic_universal_map.eval_png_apply, f.map_sum,
      FiltrationPow_map_to_fun_coe, subtype.coe_mk, pow_incl_apply, f.level_coe],
    apply fintype.sum_congr,
    intro i,
    simp only [← gsmul_eq_smul],
    exact (f.to_add_monoid_hom.map_gsmul _ _).symm
  end }

lemma eval_FP_comp (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] [(g.comp f).suitable c₁ c₃] :
  (g.comp f).eval_FP r' c₁ c₃ = f.eval_FP r' c₁ c₂ ≫ g.eval_FP r' c₂ c₃ :=
begin
  ext j s i,
  dsimp,
  simp only [eval_png₀, subtype.coe_mk],
  rw eval_png_comp,
  simp only [add_monoid_hom.coe_comp, function.comp_app],
  refl,
end

lemma cast_le_comp_eval_FP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  cast_le r' c₁ c₂ m ≫ ϕ.eval_FP r' c₂ c₄ = ϕ.eval_FP r' c₁ c₃ ≫ cast_le r' c₃ c₄ n :=
by { ext, refl }

open FiltrationPow

lemma Tinv_comp_eval_FP (r' c₁ c₂ c₃ : ℝ≥0)
  [fact (r'⁻¹ * c₁ ≤ c₂)] [fact (r'⁻¹ * c₂ ≤ c₃)] [ϕ.suitable c₁ c₂] [ϕ.suitable c₂ c₃] :
  Tinv r' c₁ c₂ m ≫ ϕ.eval_FP r' c₂ c₃ = ϕ.eval_FP r' c₁ c₂ ≫ Tinv r' c₂ c₃ n :=
begin
  ext M x : 3,
  change ϕ.eval_png₀ M c₂ c₃ ((Tinv r' c₁ c₂ m).app M x) =
    (Tinv r' c₂ c₃ n).app M (ϕ.eval_png₀ M c₁ c₂ x),
  ext j,
  dsimp only [eval_png₀],
  simp only [eval_png_apply, subtype.coe_mk, pow_incl_apply,
    FiltrationPow.Tinv, FiltrationPow_map_to_fun_coe, Pow_map_to_fun, Tinv₀_hom_to_fun, Tinv₀_coe,
    profinitely_filtered_pseudo_normed_group_hom.map_sum],
  apply fintype.sum_congr,
  intro i,
  simp only [← gsmul_eq_smul],
  exact ((profinitely_filtered_pseudo_normed_group_hom.to_add_monoid_hom _).map_gsmul _ _).symm
end

end basic_universal_map
end breen_deligne

open breen_deligne
