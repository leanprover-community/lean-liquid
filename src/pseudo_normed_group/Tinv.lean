import for_mathlib.normed_group_hom_equalizer
import pseudo_normed_group.CLC

open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group category_theory.limits
open normed_group_hom

namespace NormedGroup

def equalizer.map {V₁ V₂ W₁ W₂ : NormedGroup} {f₁ f₂ g₁ g₂} (φ : V₁ ⟶ V₂) (ψ : W₁ ⟶ W₂)
  (hf : f₁ ≫ ψ = φ ≫ f₂) (hg : g₁ ≫ ψ = φ ≫ g₂) :
  of (f₁.equalizer g₁) ⟶ of (f₂.equalizer g₂) :=
normed_group_hom.equalizer.map _ _ hf hg

end NormedGroup

universe variable u
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
variables (M M₁ M₂ M₃ : ProFiltPseuNormGrpWithTinv.{u} r')
variables (c c₁ c₂ c₃ c₄ c₅ c₆ : ℝ≥0) (l m n : ℕ)
variables (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)

/-- The "functor" that sends `M` and `c` to `V-hat((filtration M c)^n)^{T⁻¹}`,
defined by taking `T⁻¹`-invariants
for two different actions by `T⁻¹`:

* The first comes from the action of `T⁻¹` on `M`.
* The second comes from the action of `T⁻¹` on `V`.

We take the equalizer of those two actions.

See the lines just above Definition 9.3 of [Analytic]. -/
def CLCPTinv (r : ℝ≥0) (V : NormedGroup) (n : ℕ)
  [normed_with_aut r V] [fact (0 < r)] {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
  NormedGroup :=
NormedGroup.of $ normed_group_hom.equalizer
  ((CLCP V n).map f)
  ((CLCFP.T_inv' r V n).app A ≫ (CLCP V n).map g)

namespace CLCPTinv

def map {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁: f₁ ≫ ψ = ϕ ≫ f₂) (h₂ : g₁ ≫ ψ = ϕ ≫ g₂) :
  CLCPTinv r V n f₁ g₁ ⟶ CLCPTinv r V n f₂ g₂ :=
NormedGroup.equalizer.map ((CLCP V n).map ϕ) ((CLCP V n).map ψ)
  (by rw [← functor.map_comp, ← functor.map_comp, h₁]) $
by rw [← category.assoc, (CLCFP.T_inv' _ _ _).naturality,
  category.assoc, category.assoc, ← functor.map_comp, ← functor.map_comp, h₂]

@[simp] lemma map_id {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
  map r V n f g f g (𝟙 A) (𝟙 B) rfl rfl = 𝟙 _ :=
begin
  simp only [map, NormedGroup.equalizer.map, category_theory.functor.map_id],
  exact equalizer.map_id,
end

lemma map_comp {A₁ A₂ A₃ B₁ B₂ B₃ : Profiniteᵒᵖ}
  {f₁ g₁ : A₁ ⟶ B₁} {f₂ g₂ : A₂ ⟶ B₂} {f₃ g₃ : A₃ ⟶ B₃}
  (ϕ₁ : A₁ ⟶ A₂) (ϕ₂ : A₂ ⟶ A₃) (ψ₁ : B₁ ⟶ B₂) (ψ₂ : B₂ ⟶ B₃)
  (h1 h2 h3 h4 h5 h6) :
  CLCPTinv.map r V n f₁ g₁ f₃ g₃ (ϕ₁ ≫ ϕ₂) (ψ₁ ≫ ψ₂) h1 h2 =
  CLCPTinv.map r V n f₁ g₁ f₂ g₂ ϕ₁ ψ₁ h3 h4 ≫
  CLCPTinv.map r V n f₂ g₂ f₃ g₃ ϕ₂ ψ₂ h5 h6 :=
begin
  simp only [map, NormedGroup.equalizer.map, category_theory.functor.map_comp],
  exact (equalizer.map_comp_map _ _ _ _).symm,
end

lemma map_comp' {A₁ A₂ A₃ B₁ B₂ B₃ : Profiniteᵒᵖ}
  {f₁ g₁ : A₁ ⟶ B₁} {f₂ g₂ : A₂ ⟶ B₂} {f₃ g₃ : A₃ ⟶ B₃}
  (ϕ₁ : A₁ ⟶ A₂) (ϕ₂ : A₂ ⟶ A₃) (ψ₁ : B₁ ⟶ B₂) (ψ₂ : B₂ ⟶ B₃)
  (h3 h4 h5 h6) :
  CLCPTinv.map r V n f₁ g₁ f₂ g₂ ϕ₁ ψ₁ h3 h4 ≫
  CLCPTinv.map r V n f₂ g₂ f₃ g₃ ϕ₂ ψ₂ h5 h6 =
  CLCPTinv.map r V n f₁ g₁ f₃ g₃ (ϕ₁ ≫ ϕ₂) (ψ₁ ≫ ψ₂)
    (by rw [← category.assoc, h3, category.assoc, h5, ← category.assoc])
    (by rw [← category.assoc, h4, category.assoc, h6, ← category.assoc]) :=
(map_comp _ _ _ _ _ _ _ _ _ _ _ _ _).symm

end CLCPTinv
-- by haveI : fact (c₂ ≤ c) := ⟨h.1.trans $ (mul_le_mul' r1.1 le_rfl).trans (by simp)⟩; exact


/-- The "functor" that sends `M` and `c` to `V-hat((filtration M c)^n)^{T⁻¹}`,
defined by taking `T⁻¹`-invariants
for two different actions by `T⁻¹`:

* The first comes from the action of `T⁻¹` on `M`.
* The second comes from the action of `T⁻¹` on `V`.

We take the equalizer of those two actions.

See the lines just above Definition 9.3 of [Analytic]. -/
@[simps] def CLCFPTinv₂ (r : ℝ≥0) (V : NormedGroup)
  (r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [r1 : fact (r' ≤ 1)] [normed_with_aut r V]
  (c c₂ : ℝ≥0) [h : fact (c₂ ≤ r' * c)] [fact (c₂ ≤ c)]
  (n : ℕ) : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ NormedGroup :=
{ obj := λ M,
  CLCPTinv r V n
    (profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv₀_hom M.unop c₂ c).op
    (Filtration.cast_le _ _ _).op,
  map := λ M₁ M₂ f, CLCPTinv.map _ _ _ _ _ _ _
    ((ProFiltPseuNormGrpWithTinv.level _ _).op.map f)
    ((ProFiltPseuNormGrpWithTinv.level _ _).op.map f)
    (by { simp only [functor.op_map, ← op_comp],
          congr' 1, ext x, exact (f.unop.map_Tinv _).symm })
    (by { simp only [functor.op_map, ← op_comp], refl }),
  map_id' := λ M, by { simp only [category_theory.functor.map_id, op_id], apply CLCPTinv.map_id },
  map_comp' := λ M₁ M₂ M₃ f g,
    by { simp only [category_theory.functor.map_comp], apply CLCPTinv.map_comp } }
-- by haveI : fact (c₂ ≤ c) := ⟨h.1.trans $ (mul_le_mul' r1.1 le_rfl).trans (by simp)⟩; exact
-- CLCPTinv r V n
--   (profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv₀_hom M c₂ c).op
--   (Filtration.cast_le _ _ _).op

/-- The "functor" that sends `M` and `c` to `V-hat((filtration M c)^n)^{T⁻¹}`,
defined by taking `T⁻¹`-invariants
for two different actions by `T⁻¹`:

* The first comes from the action of `T⁻¹` on `M`.
* The second comes from the action of `T⁻¹` on `V`.

We take the equalizer of those two actions.

See the lines just above Definition 9.3 of [Analytic]. -/
def CLCFPTinv (r : ℝ≥0) (V : NormedGroup) (r' : ℝ≥0)
  (c : ℝ≥0) (n : ℕ) [normed_with_aut r V] [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ NormedGroup :=
CLCFPTinv₂ r V r' c (r' * c) n

namespace CLCFPTinv₂

lemma map_norm_noninc [fact (c₂ ≤ r' * c)] [fact (c₂ ≤ c)]
  {M₁ M₂} (f : M₁ ⟶ M₂) : ((CLCFPTinv₂ r V r' c c₂ n).map f).norm_noninc :=
equalizer.map_norm_noninc _ _ $ CLCFP.map_norm_noninc _ _ _ _ _

def res [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)] [fact (c₄ ≤ r' * c₃)] [fact (c₄ ≤ c₃)]
  [fact (c₃ ≤ c₁)] [fact (c₄ ≤ c₂)] : CLCFPTinv₂ r V r' c₁ c₂ n ⟶ CLCFPTinv₂ r V r' c₃ c₄ n :=
{ app := λ M,
  CLCPTinv.map _ _ _ _ _ _ _ (Filtration.cast_le _ _ _).op (Filtration.cast_le _ _ _).op
    (by { rw [← op_comp, ← op_comp], refl })
    (by { rw [← op_comp, ← op_comp], refl }),
  naturality' := λ M₁ M₂ f, begin
    rw [CLCFPTinv₂_map, CLCFPTinv₂_map, CLCPTinv.map_comp', CLCPTinv.map_comp'],
    refl,
  end }

@[simp] lemma res_refl [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)] : res r V r' c₁ c₂ c₁ c₂ n = 𝟙 _ :=
by { simp only [res, Filtration.cast_le_refl], ext x : 2, apply CLCPTinv.map_id }

lemma res_comp_res
  [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)]
  [fact (c₄ ≤ r' * c₃)] [fact (c₄ ≤ c₃)]
  [fact (c₆ ≤ r' * c₅)] [fact (c₆ ≤ c₅)]
  [fact (c₃ ≤ c₁)] [fact (c₄ ≤ c₂)]
  [fact (c₅ ≤ c₃)] [fact (c₆ ≤ c₄)]
  [fact (c₅ ≤ c₁)] [fact (c₆ ≤ c₂)] :
  res r V r' c₁ c₂ c₃ c₄ n ≫ res r V r' c₃ c₄ c₅ c₆ n = res r V r' c₁ c₂ c₅ c₆ n :=
begin
  ext x : 2, simp only [res, nat_trans.comp_app],
  exact (CLCPTinv.map_comp _ _ _ _ _ _ _ _ _ _ _ _ _).symm
end

end CLCFPTinv₂

namespace CLCFPTinv

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((CLCFPTinv r V r' c n).map f).norm_noninc :=
CLCFPTinv₂.map_norm_noninc _ _ _ _ _ _ _

def res [fact (c₂ ≤ c₁)] : CLCFPTinv r V r' c₁ n ⟶ CLCFPTinv r V r' c₂ n :=
CLCFPTinv₂.res r V r' c₁ _ c₂ _ n

@[simp] lemma res_refl : res r V r' c₁ c₁ n = 𝟙 _ :=
CLCFPTinv₂.res_refl _ _ _ _ _ _

lemma res_comp_res [fact (c₃ ≤ c₁)] [fact (c₅ ≤ c₃)] [fact (c₅ ≤ c₁)] :
  res r V r' c₁ c₃ n ≫ res r V r' c₃ c₅ n = res r V r' c₁ c₅ n :=
CLCFPTinv₂.res_comp_res _ _ _ _ _ _ _ _ _ _

end CLCFPTinv

namespace breen_deligne

open CLCFPTinv

variables (M) {l m n}

-- namespace basic_universal_map

-- variables (ϕ : basic_universal_map m n)

-- def eval_CLCFPTinv [ϕ.suitable c₁ c₂] :
--   CLCFPTinv r V r' M c₂ n ⟶ CLCFPTinv r V r' M c₁ m :=
-- equalizer.map (ϕ.eval_CLCFP _ _ _ _ _) (ϕ.eval_CLCFP _ _ _ _ _)
-- (Tinv_comp_eval_CLCFP _ _ _ _ _ _) $
-- show (CLCFP.T_inv r V r' c₂ n ≫ CLCFP.res V r' (r' * c₂) c₂ n) ≫ (eval_CLCFP V r' M (r' * c₁) (r' * c₂) ϕ) =
--     (eval_CLCFP V r' M c₁ c₂ ϕ) ≫ (CLCFP.T_inv r V r' c₁ m ≫ CLCFP.res V r' (r' * c₁) c₁ m),
-- by rw [category.assoc, res_comp_eval_CLCFP V r' M (r' * c₁) c₁ (r' * c₂) c₂,
--     ← category.assoc, T_inv_comp_eval_CLCFP, category.assoc]

-- lemma map_comp_eval_CLCFPTinv [ϕ.suitable c₁ c₂] :
--   map r V r' c₂ n f ≫ ϕ.eval_CLCFPTinv r V r' M₁ c₁ c₂ =
--     ϕ.eval_CLCFPTinv r V r' M₂ c₁ c₂ ≫ map r V r' c₁ m f :=
-- calc _ = _ : equalizer.map_comp_map _ _ _ _
--    ... = _ : by { congr' 1; apply map_comp_eval_CLCFP }
--    ... = _ : (equalizer.map_comp_map _ _ _ _).symm

-- lemma res_comp_eval_CLCFPTinv
--   [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
--   res r V r' c₃ c₄ n ≫ ϕ.eval_CLCFPTinv r V r' M c₁ c₃ =
--     ϕ.eval_CLCFPTinv r V r' M c₂ c₄ ≫ res r V r' c₁ c₂ m :=
-- calc _ = _ : equalizer.map_comp_map _ _ _ _
--    ... = _ : by { congr' 1; apply res_comp_eval_CLCFP }
--    ... = _ : (equalizer.map_comp_map _ _ _ _).symm

-- end basic_universal_map

namespace universal_map

variables (ϕ : universal_map m n)

def eval_CLCFPTinv₂
  [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)] [fact (c₄ ≤ r' * c₃)] [fact (c₄ ≤ c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂] :
  CLCFPTinv₂ r V r' c₁ c₂ n ⟶ CLCFPTinv₂ r V r' c₃ c₄ m :=
{ app := λ M, begin
    refine NormedGroup.equalizer.map
      ((ϕ.eval_CLCFP _ _ _ _).app _ : _)
      ((ϕ.eval_CLCFP _ _ _ _).app _ : _) _ _,
    { have := Tinv_comp_eval_CLCFP V r' c₁ c₂ c₃ c₄ ϕ,
      apply_fun λ x, nat_trans.app x M at this,
      rw [nat_trans.comp_app, nat_trans.comp_app] at this,
      exact this },
    { have := res_comp_eval_CLCFP V r' c₁ c₂ c₃ c₄ ϕ,
      apply_fun λ x, nat_trans.app x M at this,
      rw [nat_trans.comp_app, nat_trans.comp_app, CLCFP.res_app'] at this,
      rw [category.assoc, this], clear this,
      have := T_inv_comp_eval_CLCFP r V r' c₁ c₃ ϕ,
      apply_fun λ x, nat_trans.app x M at this,
      rw [nat_trans.comp_app, nat_trans.comp_app, CLCFP.T_inv,
        whisker_left_app] at this,
      change (CLCFP.T_inv' r V n).app (op (filtration_obj ↥(unop M) c₁)) ≫ _ = _ at this,
      rw [← category.assoc, this, category.assoc], refl }
  end,
  naturality' := _ }

def eval_CLCFPTinv [ϕ.suitable c₁ c₂] :
  CLCFPTinv r V r' c₂ n ⟶ CLCFPTinv r V r' c₁ m :=
{ app := λ M, begin
    refine NormedGroup.equalizer.map
      ((ϕ.eval_CLCFP _ _ _ _).app _ : _)
      ((ϕ.eval_CLCFP _ _ _ _).app _ : _) _ _,
    -- refine (ϕ.eval_CLCFP _ _ _ _).app _,
    have := Tinv_comp_eval_CLCFP,
  end,
  naturality' := _ }

.

equalizer.map (ϕ.eval_CLCFP _ _ _ _ _) (ϕ.eval_CLCFP _ _ _ _ _)
(Tinv_comp_eval_CLCFP _ _ _ _ _ _) $
show (CLCFP.T_inv r V r' c₂ n ≫ CLCFP.res V r' (r' * c₂) c₂ n) ≫ (eval_CLCFP V r' M (r' * c₁) (r' * c₂) ϕ) =
     (eval_CLCFP V r' M c₁ c₂ ϕ) ≫ (CLCFP.T_inv r V r' c₁ m ≫ CLCFP.res V r' (r' * c₁) c₁ m),
by rw [category.assoc, res_comp_eval_CLCFP V r' M (r' * c₁) c₁ (r' * c₂) c₂,
    ← category.assoc, T_inv_comp_eval_CLCFP, category.assoc]

@[simp] lemma eval_CLCFPTinv_zero :
  (0 : universal_map m n).eval_CLCFPTinv r V r' M c₁ c₂ = 0 :=
by { simp only [eval_CLCFPTinv, eval_CLCFP_zero, equalizer.map_ι], ext, refl }

open category_theory.limits

lemma eval_CLCFPTinv_comp {l m n : FreeMat} (g : m ⟶ n) (f : l ⟶ m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] [(comp g f).suitable c₁ c₃] :
  (f ≫ g).eval_CLCFPTinv r V r' M c₁ c₃ =
    g.eval_CLCFPTinv r V r' M c₂ c₃ ≫ f.eval_CLCFPTinv r V r' M c₁ c₂ :=
calc _ = _ : by { delta eval_CLCFPTinv, congr' 1; apply eval_CLCFP_comp }
   ... = _ : (equalizer.map_comp_map _ _ _ _).symm

lemma map_comp_eval_CLCFPTinv [ϕ.suitable c₁ c₂] :
  map r V r' c₂ n f ≫ ϕ.eval_CLCFPTinv r V r' M₁ c₁ c₂ =
    ϕ.eval_CLCFPTinv r V r' M₂ c₁ c₂ ≫ map r V r' c₁ m f :=
calc _ = _ : equalizer.map_comp_map _ _ _ _
   ... = _ : by { congr' 1; apply map_comp_eval_CLCFP }
   ... = _ : (equalizer.map_comp_map _ _ _ _).symm

lemma res_comp_eval_CLCFPTinv
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  res r V r' c₃ c₄ n ≫ ϕ.eval_CLCFPTinv r V r' M c₁ c₃ =
    ϕ.eval_CLCFPTinv r V r' M c₂ c₄ ≫ res r V r' c₁ c₂ m :=
calc _ = _ : equalizer.map_comp_map _ _ _ _
   ... = _ : by { congr' 1; apply res_comp_eval_CLCFP }
   ... = _ : (equalizer.map_comp_map _ _ _ _).symm

end universal_map

end breen_deligne
