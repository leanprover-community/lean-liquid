import pseudo_normed_group.breen_deligne
import for_mathlib.SemiNormedGroup

/-!

# Constructions on the filtration on a profinitely filtered pseudo-normed group

## Main definitions

- `FiltrationPow r' c n`: the functor sending a profinitely filtered `M` to `M_c^n`.
- `φ.eval_FP r' c₁ c₂`: The map M_c₁^m → M_c₂^n induced by a (c₁, c₂)-suitable φ.

-/
open_locale classical nnreal big_operators kronecker
noncomputable theory
local attribute [instance] type_pow

universe variables u

@[simps]
def pseudo_normed_group.filtration_obj
  (M) [profinitely_filtered_pseudo_normed_group M] (c) : Profinite :=
Profinite.of (pseudo_normed_group.filtration M c)

open profinitely_filtered_pseudo_normed_group category_theory
  comphaus_filtered_pseudo_normed_group

namespace Filtration
variables (M : Type u) [profinitely_filtered_pseudo_normed_group M]
@[simps]
def cast_le (c₁ c₂ : ℝ≥0) [h : fact (c₁ ≤ c₂)] :
  pseudo_normed_group.filtration_obj.{u} M c₁ ⟶ pseudo_normed_group.filtration_obj.{u} M c₂ :=
{ to_fun := pseudo_normed_group.cast_le,
  continuous_to_fun := continuous_cast_le c₁ c₂ }

theorem cast_le_refl (c : ℝ≥0) : cast_le M c c = 𝟙 _ := by { ext, refl }

theorem cast_le_comp (c₁ c₂ c₃ : ℝ≥0) [h₁ : fact (c₁ ≤ c₂)] [h₂ : fact (c₂ ≤ c₃)] :
  cast_le M c₁ c₂ ≫ cast_le M c₂ c₃ = @cast_le M _ c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ :=
by { ext, refl }

end Filtration

@[simps obj_obj obj_map_to_fun map_app {fully_applied := ff}]
def Filtration (r' : ℝ≥0) : ℝ≥0 ⥤ ProFiltPseuNormGrpWithTinv.{u} r' ⥤ Profinite.{u} :=
{ obj := λ c,
  { obj := λ M, pseudo_normed_group.filtration_obj M c,
    map := λ M N f, ⟨f.level c, f.level_continuous c⟩,
    map_id' := by { intros, ext, refl },
    map_comp' := by { intros, ext, refl } },
  map := λ c₁ c₂ h,
  { app := λ M, @Filtration.cast_le _ _ c₁ c₂ ⟨le_of_hom h⟩ },
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

open SemiNormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group
open profinitely_filtered_pseudo_normed_group_with_Tinv

/-- The functor that sends `A` to `A^n` -/
@[simps obj map]
def Pow (n : ℕ) : Profinite ⥤ Profinite :=
{ obj := λ A, of (A^n),
  map := λ A B f, {
    to_fun := λ x j, f (x j),
    continuous_to_fun := continuous_pi $ λ j, f.2.comp (continuous_apply j) } }

@[simps]
def Pow_Pow_X (N n : ℕ) (X) : (Pow N ⋙ Pow n).obj X ≅ (Pow (N * n)).obj X :=
Profinite.iso_of_homeo
{ to_equiv := (equiv.curry _ _ _).symm.trans (((equiv.prod_comm _ _).trans fin_prod_fin_equiv).arrow_congr (equiv.refl X)),
  continuous_to_fun :=
  begin
    apply continuous_pi,
    intro ij,
    let k := ((equiv.prod_comm _ _).trans fin_prod_fin_equiv).symm ij,
    convert (@continuous_apply _ (λ i, X) _ k.2).comp (@continuous_apply _ (λ i, (X^N)) _ k.1),
  end,
  continuous_inv_fun :=
  begin
    apply continuous_pi,
    intro i,
    refine continuous_pi _,
    intro j,
    exact continuous_apply _,
  end }
.

@[simps hom inv]
def Pow_mul (N n : ℕ) : Pow (N * n) ≅ Pow N ⋙ Pow n :=
nat_iso.of_components (λ X, (Pow_Pow_X N n X).symm)
begin
  intros X Y f,
  ext x i j,
  refl,
end

@[simps]
def profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv₀_hom
  {r' : ℝ≥0} (M : Type*) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]
  (c c₂ : ℝ≥0) [fact (c ≤ r' * c₂)] : filtration_obj M c ⟶ filtration_obj M c₂ :=
by exact ⟨Tinv₀ c c₂, Tinv₀_continuous _ _⟩

open profinitely_filtered_pseudo_normed_group_with_Tinv

namespace Filtration

@[simps]
def res (r' c₁ c₂ : ℝ≥0) [h : fact (c₁ ≤ c₂)] :
  (Filtration r').obj c₁ ⟶ (Filtration r').obj c₂ :=
(Filtration r').map (hom_of_le h.1)

theorem res_refl (r' c : ℝ≥0) : res r' c c = 𝟙 _ := by { ext, refl }

theorem res_comp (r' c₁ c₂ c₃ : ℝ≥0) [h₁ : fact (c₁ ≤ c₂)] [h₂ : fact (c₂ ≤ c₃)] :
  res r' c₁ c₂ ≫ res r' c₂ c₃ = @res r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ :=
by { ext, refl }

@[simps] def Tinv₀ {r' : ℝ≥0} (c c₂ : ℝ≥0) [fact (c ≤ r' * c₂)] :
  (Filtration.{u} r').obj c ⟶ (Filtration r').obj c₂ :=
{ app := λ M, Tinv₀_hom M c c₂,
  naturality' := λ M₁ M₂ f, by { ext x, exact (f.map_Tinv _).symm } }

theorem Tinv₀_comp_res {r' : ℝ≥0} (c₁ c₂ c₃ c₄ : ℝ≥0)
  [fact (c₁ ≤ r' * c₂)] [fact (c₃ ≤ r' * c₄)] [fact (c₂ ≤ c₄)] [fact (c₁ ≤ c₃)] :
  Tinv₀ c₁ c₂ ≫ res r' c₂ c₄ = res r' c₁ c₃ ≫ Tinv₀ c₃ c₄ := rfl

def pi_iso (r' c : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv r') (N : ℕ) :
  Profinite.of (filtration (M^N) c) ≅ Profinite.of ((filtration M c)^N) :=
Profinite.iso_of_homeo $ filtration_pi_homeo _ _

end Filtration


/-- `FiltrationPow r' c n` is the functor sending a profinitely filtered `M` to `M_c^n`. -/
@[simps obj map {fully_applied := ff}]
def FiltrationPow (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  ProFiltPseuNormGrpWithTinv r' ⥤ Profinite :=
ProFiltPseuNormGrpWithTinv.Pow r' n ⋙ (Filtration r').obj c

namespace FiltrationPow

@[simps]
def cast_le (r' c₁ c₂ : ℝ≥0) [fact (c₁ ≤ c₂)] (n : ℕ) :
  FiltrationPow.{u} r' c₁ n ⟶ FiltrationPow r' c₂ n :=
{ app := λ M, (Filtration.cast_le _ c₁ c₂),
  naturality' := λ M N f, by { ext, refl } }

theorem cast_le_refl (r' c : ℝ≥0) (n : ℕ) : cast_le r' c c n = 𝟙 _ :=
by { ext, refl }

theorem cast_le_comp (r' c₁ c₂ c₃ : ℝ≥0) [h₁ : fact (c₁ ≤ c₂)] [h₂ : fact (c₂ ≤ c₃)] (n : ℕ) :
  cast_le r' c₁ c₂ n ≫ cast_le r' c₂ c₃ n =
  @cast_le r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n :=
by { ext, refl }

@[simps]
def Tinv (r' : ℝ≥0) (c c₂) [fact (c ≤ r' * c₂)] (n) :
  FiltrationPow r' c n ⟶ FiltrationPow r' c₂ n :=
whisker_left _ (Filtration.Tinv₀ c c₂)

lemma Tinv_app (r' : ℝ≥0) (c c₂) [fact (c ≤ r' * c₂)] (n M) :
  (Tinv r' c c₂ n).app M = (Tinv₀_hom _ c c₂) := rfl

lemma cast_le_vcomp_Tinv (r' c₁ c₂ c₃ : ℝ≥0)
  [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ r' * c₂)] [fact (c₂ ≤ r' * c₃)] (n : ℕ) :
  cast_le r' c₁ c₂ n ≫ Tinv r' c₂ c₃ n = Tinv r' c₁ c₂ n ≫ cast_le r' c₂ c₃ n :=
by { ext, refl }

@[simps hom inv]
def mul_iso (r' c : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv r') (N n : ℕ) :
  (FiltrationPow r' c n).obj (ProFiltPseuNormGrpWithTinv.of r' (↥M ^ N)) ≅
  (FiltrationPow r' c (N * n)).obj M :=
((Filtration r').obj c).map_iso $ (ProFiltPseuNormGrpWithTinv.Pow_mul r' N n).symm.app _

end FiltrationPow

namespace breen_deligne
namespace basic_universal_map

variables (r' c c₁ c₂ c₃ c₄ : ℝ≥0) {l m n : ℕ} (ϕ : basic_universal_map m n)

open FiltrationPow profinitely_filtered_pseudo_normed_group_with_Tinv_hom

@[simps]
def eval_FP [ϕ.suitable c₁ c₂] : FiltrationPow.{u} r' c₁ m ⟶ FiltrationPow r' c₂ n :=
{ app := λ M,
  { to_fun := ϕ.eval_png₀ M c₁ c₂,
    continuous_to_fun := ϕ.eval_png₀_continuous M c₁ c₂ },
  naturality' := λ M₁ M₂ f, begin
    ext1 x,
    change ϕ.eval_png₀ M₂ c₁ c₂ ((FiltrationPow r' c₁ m).map f x) =
      (FiltrationPow r' c₂ n).map f (ϕ.eval_png₀ M₁ c₁ c₂ x),
    ext j,
    dsimp only [FiltrationPow_map, Filtration_obj_map_to_fun,basic_universal_map.eval_png₀_coe,
      profinitely_filtered_pseudo_normed_group_with_Tinv_hom.level_coe,
      comp_to_fun, coe_to_add_monoid_hom],
    simp only [basic_universal_map.eval_png_apply, pi_map_to_fun, f.map_sum, f.map_gsmul],
  end }

lemma eval_FP_comp (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂]
  [(basic_universal_map.comp g f).suitable c₁ c₃] :
  (basic_universal_map.comp g f).eval_FP r' c₁ c₃ = f.eval_FP r' c₁ c₂ ≫ g.eval_FP r' c₂ c₃ :=
by { ext, dsimp, rw eval_png_comp, refl }

lemma cast_le_comp_eval_FP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  cast_le r' c₁ c₂ m ≫ ϕ.eval_FP r' c₂ c₄ = ϕ.eval_FP r' c₁ c₃ ≫ cast_le r' c₃ c₄ n :=
by { ext, refl }

open FiltrationPow

lemma Tinv_comp_eval_FP (r' c₁ c₂ c₃ c₄ : ℝ≥0)
  [fact (c₁ ≤ r' * c₂)] [fact (c₃ ≤ r' * c₄)] [ϕ.suitable c₁ c₃] [ϕ.suitable c₂ c₄] :
  Tinv r' c₁ c₂ m ≫ ϕ.eval_FP r' c₂ c₄ = ϕ.eval_FP r' c₁ c₃ ≫ Tinv r' c₃ c₄ n :=
begin
  ext M x : 3,
  change ϕ.eval_png₀ M c₂ c₄ ((Tinv r' c₁ c₂ m).app M x) =
    (Tinv r' c₃ c₄ n).app M (ϕ.eval_png₀ M c₁ c₃ x),
  ext j,
  dsimp,
  simp only [eval_png_apply, comphaus_filtered_pseudo_normed_group_hom.map_sum,
    comphaus_filtered_pseudo_normed_group_hom.map_gsmul, pi_Tinv_apply],
end
.

lemma mul_iso_eval_FP (N : ℕ) [ϕ.suitable c₂ c₁] (M) :
  (FiltrationPow.mul_iso.{u u} r' c₂ M N m).inv ≫
    (basic_universal_map.eval_FP r' c₂ c₁ ϕ).app (ProFiltPseuNormGrpWithTinv.of r' (M ^ N)) =
  (basic_universal_map.eval_FP r' c₂ c₁ ((basic_universal_map.mul N) ϕ)).app M ≫
    (FiltrationPow.mul_iso.{u u} r' c₁ M N n).inv :=
begin
  ext x i j,
  dsimp [mul],
  simp only [eval_png_apply, equiv.symm_apply_apply, matrix.minor_apply, matrix.kronecker],
  rw [← fin_prod_fin_equiv.sum_comp, ← finset.univ_product_univ, finset.sum_product,
      finset.sum_comm],
  simp only [equiv.symm_apply_apply, matrix.one_apply, boole_mul, ite_smul, zero_smul,
    finset.sum_ite_eq, finset.mem_univ, if_true, matrix.kronecker_map, matrix.kronecker_apply],
  convert finset.sum_apply j (finset.univ : finset (fin m)) _ using 1,
end

end basic_universal_map

end breen_deligne
