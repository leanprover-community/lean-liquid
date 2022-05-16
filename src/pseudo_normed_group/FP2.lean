import breen_deligne.constants
import breen_deligne.suitable
import pseudo_normed_group.FP
import system_of_complexes.rescale

noncomputable theory

open_locale classical nnreal big_operators
local attribute [instance] type_pow

universe variable u

namespace category_theory
namespace FreeAb

def of_functor (C : Type*) [category C] : C ⥤ FreeAb C :=
{ obj := of,
  map := λ X Y f, free_abelian_group.of f,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl }

end FreeAb
end category_theory

open category_theory breen_deligne

namespace breen_deligne

variables (r' : ℝ≥0)
variables (BD : breen_deligne.data)
variables (M : ProFiltPseuNormGrpWithTinv r')
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

open category_theory breen_deligne
open Profinite pseudo_normed_group profinitely_filtered_pseudo_normed_group

/-- The "functor" that sends `M` and `c` to `(filtration M c)^n` -/
def FP2 (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  ProFiltPseuNormGrpWithTinv r' ⥤ FreeAb Profinite :=
FiltrationPow r' c n ⋙ FreeAb.of_functor _

theorem FP2_def (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  FP2 r' c n = FiltrationPow r' c n ⋙ FreeAb.of_functor _ := rfl

namespace FP2

@[simps {fully_applied := ff}]
def res (r' : ℝ≥0) (c₁ c₂ : ℝ≥0) [fact (c₁ ≤ c₂)] (n : ℕ) : FP2 r' c₁ n ⟶ FP2 r' c₂ n :=
whisker_right (FiltrationPow.cast_le r' c₁ c₂ n) _

@[simp] lemma res_refl : res r' c c n = 𝟙 _ :=
by { simp [res, FiltrationPow.cast_le_refl], refl }

lemma res_comp_res [h₁ : fact (c₁ ≤ c₂)] [h₂ : fact (c₂ ≤ c₃)] :
  res r' c₁ c₂ n ≫ res r' c₂ c₃ n = @res r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n :=
by simp only [res, ← whisker_right_comp, FiltrationPow.cast_le_comp]

section Tinv
open profinitely_filtered_pseudo_normed_group_with_Tinv
variables [fact (0 < r')]

@[simps {fully_applied := ff}]
def Tinv [fact (c₁ ≤ r' * c₂)] : FP2 r' c₁ n ⟶ FP2 r' c₂ n :=
whisker_right (FiltrationPow.Tinv r' c₁ c₂ n) _

lemma Tinv_def [fact (c₁ ≤ r' * c₂)] :
  Tinv r' c₁ c₂ n = whisker_right (FiltrationPow.Tinv r' c₁ c₂ n) _ := rfl

lemma res_comp_Tinv
  [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ r' * c₂)] [fact (c₂ ≤ r' * c₃)] :
  res r' c₁ c₂ n ≫ Tinv r' c₂ c₃ n = Tinv r' c₁ c₂ n ≫ res r' c₂ c₃ n :=
by { simp only [Tinv, res, ← whisker_right_comp], refl }

end Tinv

end FP2

open FP2

variables {l m n}

namespace basic_universal_map

open basic_universal_map

variables (ϕ : basic_universal_map m n)

def eval_FP2 (c₁ c₂ : ℝ≥0) [ϕ.suitable c₁ c₂] : FP2 r' c₁ m ⟶ FP2 r' c₂ n :=
whisker_right (ϕ.eval_FP r' c₁ c₂) _

def eval_FP2' (c₁ c₂ : ℝ≥0) : FP2 r' c₁ m ⟶ FP2 r' c₂ n :=
if H : ϕ.suitable c₁ c₂
then by exactI whisker_right (ϕ.eval_FP r' c₁ c₂) _
else 0

lemma eval_FP2_eq_eval_FP2' (h : ϕ.suitable c₁ c₂) :
  eval_FP2 r' ϕ c₁ c₂ = eval_FP2' r' ϕ c₁ c₂ :=
by { delta eval_FP2 eval_FP2', rw dif_pos h }

lemma eval_FP2'_def [h : ϕ.suitable c₁ c₂] :
  eval_FP2' r' ϕ c₁ c₂ = whisker_right (ϕ.eval_FP r' c₁ c₂) _ :=
dif_pos h

lemma eval_FP2'_not_suitable (h : ¬ ϕ.suitable c₁ c₂) :
  eval_FP2' r' ϕ c₁ c₂ = 0 :=
dif_neg h

lemma eval_FP2'_comp (f : basic_universal_map l m) (g : basic_universal_map m n)
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₂ c₃] :
  eval_FP2' r' (comp g f) c₁ c₃ = eval_FP2' r' f c₁ c₂ ≫ eval_FP2' r' g c₂ c₃ :=
begin
  haveI : (comp g f).suitable c₁ c₃ := suitable_comp c₂,
  simp only [eval_FP2'_def, eval_FP_comp r' _ c₂, whisker_right_comp]
end

lemma eval_FP2_comp (f : basic_universal_map l m) (g : basic_universal_map m n)
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₂ c₃] :
  @eval_FP2 r' _ _ (comp g f) c₁ c₃ (suitable_comp c₂) =
    eval_FP2 r' f c₁ c₂ ≫ eval_FP2 r' g c₂ c₃ :=
by { simp only [eval_FP2_eq_eval_FP2'], apply eval_FP2'_comp }

lemma res_comp_eval_FP2
  [fact (c₁ ≤ c₂)] [fact (c₃ ≤ c₄)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] :
  res r' c₁ c₂ m ≫ eval_FP2 r' ϕ c₂ c₄ = eval_FP2 r' ϕ c₁ c₃ ≫ res r' c₃ c₄ n :=
by simp only [res, eval_FP2, ← whisker_right_comp,
  cast_le_comp_eval_FP _ c₁ c₂ c₃ c₄]

lemma Tinv_comp_eval_FP2 [fact (0 < r')] [fact (c₁ ≤ r' * c₂)] [fact (c₃ ≤ r' * c₄)]
  [ϕ.suitable c₁ c₃] [ϕ.suitable c₂ c₄] :
  Tinv r' c₁ c₂ m ≫ eval_FP2 r' ϕ c₂ c₄ = eval_FP2 r' ϕ c₁ c₃ ≫ Tinv r' c₃ c₄ n :=
by simp only [Tinv, eval_FP2, ← whisker_right_comp,
  Tinv_comp_eval_FP _ _ c₁ c₂ c₃ c₄]

end basic_universal_map

namespace universal_map

open free_abelian_group

variables (ϕ : universal_map m n)

def eval_FP2 [ϕ.suitable c₁ c₂] : FP2 r' c₁ m ⟶ FP2 r' c₂ n :=
∑ g : {g : basic_universal_map m n // g ∈ ϕ.support},
  begin
    haveI := suitable_of_mem_support ϕ c₁ c₂ g g.2,
    exact coeff (g : basic_universal_map m n) ϕ • (basic_universal_map.eval_FP2 r' g c₁ c₂)
  end

def eval_FP2' : FP2 r' c₁ m ⟶ FP2 r' c₂ n :=
∑ g in ϕ.support, coeff g ϕ • (g.eval_FP2' r' c₁ c₂)

lemma eval_FP2_eq_eval_FP2' (h : ϕ.suitable c₁ c₂) :
  eval_FP2 r' c₁ c₂ ϕ = eval_FP2' r' c₁ c₂ ϕ :=
begin
  simp only [eval_FP2, eval_FP2', basic_universal_map.eval_FP2_eq_eval_FP2',
    subtype.val_eq_coe],
  symmetry,
  apply finset.sum_subtype ϕ.support (λ _, iff.rfl),
end

@[simp] lemma eval_FP2'_of (f : basic_universal_map m n) :
  eval_FP2' r' c₁ c₂ (of f) = f.eval_FP2' r' c₁ c₂ :=
by simp only [eval_FP2', support_of, coeff_of_self, one_smul, finset.sum_singleton]

@[simp] lemma eval_FP2_of (f : basic_universal_map m n) [f.suitable c₁ c₂] :
  eval_FP2 r' c₁ c₂ (of f) = f.eval_FP2 r' c₁ c₂ :=
by rw [eval_FP2_eq_eval_FP2', eval_FP2'_of, basic_universal_map.eval_FP2_eq_eval_FP2']

@[simp] lemma eval_FP2'_zero :
  eval_FP2' r' c₁ c₂ (0 : universal_map m n) = 0 :=
by rw [eval_FP2', support_zero, finset.sum_empty]

@[simp] lemma eval_FP2_zero :
  eval_FP2 r' c₁ c₂ (0 : universal_map m n) = 0 :=
by rw [eval_FP2_eq_eval_FP2', eval_FP2'_zero]

@[simp] lemma eval_FP2'_neg (f : universal_map m n) :
  eval_FP2' r' c₁ c₂ (-f) = -eval_FP2' r' c₁ c₂ f :=
by simp only [eval_FP2', add_monoid_hom.map_neg, finset.sum_neg_distrib, neg_smul, support_neg]

@[simp] lemma eval_FP2_neg (f : universal_map m n) [f.suitable c₁ c₂] :
  eval_FP2 r' c₁ c₂ (-f) = -eval_FP2 r' c₁ c₂ f :=
by simp only [eval_FP2_eq_eval_FP2', eval_FP2'_neg]

lemma eval_FP2'_add (f g : universal_map m n) :
  eval_FP2' r' c₁ c₂ (f + g) = eval_FP2' r' c₁ c₂ f + eval_FP2' r' c₁ c₂ g :=
begin
  simp only [eval_FP2'],
  rw finset.sum_subset (support_add f g), -- two goals
  simp only [add_monoid_hom.map_add _ f g, add_smul],
  convert finset.sum_add_distrib using 2, -- three goals
  apply finset.sum_subset (finset.subset_union_left _ _), swap,
  apply finset.sum_subset (finset.subset_union_right _ _),
  all_goals { rintros x - h, rw not_mem_support_iff at h, simp [h] },
end

lemma eval_FP2_add (f g : universal_map m n) [f.suitable c₁ c₂] [g.suitable c₁ c₂] :
  eval_FP2 r' c₁ c₂ (f + g) = eval_FP2 r' c₁ c₂ f + eval_FP2 r' c₁ c₂ g :=
by simp only [eval_FP2_eq_eval_FP2', eval_FP2'_add]

lemma eval_FP2_sub (f g : universal_map m n) [f.suitable c₁ c₂] [g.suitable c₁ c₂] :
  eval_FP2 r' c₁ c₂ (f - g) = eval_FP2 r' c₁ c₂ f - eval_FP2 r' c₁ c₂ g :=
by simp only [sub_eq_add_neg, eval_FP2_add, eval_FP2_neg]

lemma eval_FP2'_comp_of (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₂ c₃] :
  eval_FP2' r' c₁ c₃ ((universal_map.comp (of g)) (of f)) =
    eval_FP2' r' c₁ c₂ (of f) ≫ eval_FP2' r' c₂ c₃ (of g) :=
begin
  simp only [universal_map.comp_of, eval_FP2'_of],
  haveI hfg : (basic_universal_map.comp g f).suitable c₁ c₃ := basic_universal_map.suitable_comp c₂,
  rw ← basic_universal_map.eval_FP2'_comp,
end

open category_theory category_theory.limits category_theory.preadditive

lemma eval_FP2'_comp (g : universal_map m n) (f : universal_map l m)
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₂ c₃] :
  eval_FP2' r' c₁ c₃ (universal_map.comp g f) = eval_FP2' r' c₁ c₂ f ≫ eval_FP2' r' c₂ c₃ g :=
begin
  unfreezingI { revert hg },
  apply free_abelian_group.induction_on_free_predicate
    (universal_map.suitable c₁ c₂) (universal_map.suitable_free_predicate c₁ c₂) f hf;
      unfreezingI { clear_dependent f },
  { intros h₂,
    simp only [eval_FP2'_zero, zero_comp, pi.zero_apply,
      add_monoid_hom.zero_apply, add_monoid_hom.map_zero] },
  { intros f hf hg,
    -- now do another nested induction on `f`
    apply free_abelian_group.induction_on_free_predicate
      (universal_map.suitable c₂ c₃) (universal_map.suitable_free_predicate c₂ c₃) g hg;
        unfreezingI { clear_dependent g },
    { simp only [universal_map.eval_FP2'_zero, comp_zero, add_monoid_hom.map_zero,
        add_monoid_hom.zero_apply] },
    { intros g hg,
      rw suitable_of_iff at hf hg,
      resetI,
      apply eval_FP2'_comp_of },
    { intros g hg IH,
      simp only [IH, eval_FP2'_neg, add_monoid_hom.map_neg, comp_neg,
        add_monoid_hom.neg_apply] },
    { rintros (g₁ : universal_map m n) (g₂ : universal_map m n) hg₁ hg₂ IH₁ IH₂, resetI,
      haveI Hg₁f : (universal_map.comp g₁ (of f)).suitable c₁ c₃ := suitable.comp c₂,
      haveI Hg₂f : (universal_map.comp g₂ (of f)).suitable c₁ c₃ := suitable.comp c₂,
      simp only [add_monoid_hom.map_add, eval_FP2'_add, IH₁, IH₂, comp_add,
        add_monoid_hom.add_apply] } },
  { intros f hf IH hg, resetI, specialize IH,
    simp only [IH, add_monoid_hom.map_neg, eval_FP2'_neg,
      add_monoid_hom.neg_apply, neg_inj, neg_comp] },
  { rintros (f₁ : universal_map l m) (f₂ : universal_map l m) hf₁ hf₂ IH₁ IH₂ hf, resetI,
    haveI Hgf₁ : (universal_map.comp g f₁).suitable c₁ c₃ := suitable.comp c₂,
    haveI Hgf₂ : (universal_map.comp g f₂).suitable c₁ c₃ := suitable.comp c₂,
    simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply, eval_FP2'_add, IH₁, IH₂, add_comp] }
end

lemma eval_FP2_comp (g : universal_map m n) (f : universal_map l m)
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₂ c₃] :
  @eval_FP2 r' c₁ c₃ _ _ (universal_map.comp g f) (universal_map.suitable.comp c₂) =
    eval_FP2 r' c₁ c₂ f ≫ eval_FP2 r' c₂ c₃ g :=
by { simp only [eval_FP2_eq_eval_FP2'], apply eval_FP2'_comp }

lemma res_comp_eval_FP2 [fact (c₁ ≤ c₂)] [fact (c₃ ≤ c₄)] [ϕ.suitable c₁ c₃] [ϕ.suitable c₂ c₄] :
  res r' c₁ c₂ m ≫ eval_FP2 r' c₂ c₄ ϕ = eval_FP2 r' c₁ c₃ ϕ ≫ res r' c₃ c₄ n :=
begin
  simp only [eval_FP2, comp_sum, sum_comp, comp_zsmul, zsmul_comp],
  apply finset.sum_congr rfl,
  rintros ⟨g, hg⟩ -,
  haveI : g.suitable c₁ c₃ := suitable_of_mem_support ϕ _ _ g hg,
  haveI : g.suitable c₂ c₄ := suitable_of_mem_support ϕ _ _ g hg,
  simp only [subtype.coe_mk, g.res_comp_eval_FP2 r' c₁ c₂ c₃ c₄],
end

lemma Tinv_comp_eval_FP2 [fact (0 < r')] [fact (c₁ ≤ r' * c₂)] [fact (c₃ ≤ r' * c₄)]
  [ϕ.suitable c₁ c₃] [ϕ.suitable c₂ c₄] :
  Tinv r' c₁ c₂ m ≫ eval_FP2 r' c₂ c₄ ϕ = eval_FP2 r' c₁ c₃ ϕ ≫ Tinv r' c₃ c₄ n :=
begin
  simp only [eval_FP2, comp_sum, sum_comp, comp_zsmul, zsmul_comp],
  apply finset.sum_congr rfl,
  rintros ⟨g, hg⟩ -,
  haveI : g.suitable c₁ c₃ := suitable_of_mem_support ϕ _ _ g hg,
  haveI : g.suitable c₂ c₄ := suitable_of_mem_support ϕ _ _ g hg,
  congr' 1, apply basic_universal_map.Tinv_comp_eval_FP2 r',
end

end universal_map


variables (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.suitable (κ c)]

def FPsystem.X (c : ℝ≥0) (n : ℕ) : FreeAb Profinite :=
FreeAb.of $ (FiltrationPow r' (κ c n) $ BD.X n).obj M

def FPsystem.d (c : ℝ≥0) (n : ℕ) :
  FPsystem.X r' BD M κ c (n + 1) ⟶ FPsystem.X r' BD M κ c n :=
(universal_map.eval_FP2 r' (κ c (n+1)) (κ c n) (BD.d (n+1) n)).app M

lemma FPsystem.d_comp_d (c : ℝ≥0) (n : ℕ) :
  FPsystem.d r' BD M κ c (n + 1) ≫ FPsystem.d r' BD M κ c n = 0 :=
begin
  delta FPsystem.d,
  rw [← nat_trans.comp_app, ← universal_map.eval_FP2_comp],
  convert nat_trans.app_zero _, refl, refl,
  convert universal_map.eval_FP2_zero _ _ _,
  show BD.d _ _ ≫ BD.d _ _ = 0,
  rw homological_complex.d_comp_d,
end

open opposite

def FPsystem [hκ : ∀ n, fact (monotone (function.swap κ n))] :
  ℝ≥0 ⥤ chain_complex (FreeAb Profinite) ℕ :=
{ obj := λ c, chain_complex.of (FPsystem.X r' BD M κ c) (FPsystem.d r' BD M κ _) (FPsystem.d_comp_d _ _ _ _ _),
  map := λ c₁ c₂ h,
  { f := λ n, by { refine (@FP2.res r' _ _ (id _) (BD.X n)).app M,
      have := (hκ n).out, refine ⟨this h.le⟩, },
    comm' := begin
      rintro i j (rfl : j + 1 = i),
      rw [chain_complex.of_d, chain_complex.of_d],
      delta FPsystem.d, rw [← nat_trans.comp_app, ← nat_trans.comp_app],
      congr' 1,
      apply universal_map.res_comp_eval_FP2,
    end },
  map_id' := λ c, begin
    ext n, dsimp, rw [Filtration.cast_le_refl, (FreeAb.of_functor _).map_id], refl,
  end,
  map_comp' := λ c₁ c₂ c₃ h₁₂ h₂₃, begin
    ext n, dsimp, rw [← (FreeAb.of_functor _).map_comp, Filtration.cast_le_comp],
  end }
.

def FPsystem.Tinv [fact (0 < r')]
  (κ₁ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
  [∀ c, BD.suitable (κ₁ c)] [∀ c, BD.suitable (κ₂ c)]
  [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))]
  [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ r' * κ₂ c n)] :
  FPsystem r' BD M κ₁ ⟶ FPsystem r' BD M κ₂ :=
{ app := λ c,
  { f := λ n, (FP2.Tinv r' _ _ _).app M,
    comm' := begin
      rintro i j (rfl : j + 1 = i),
      dsimp only [functor.comp_obj, FPsystem],
      rw [chain_complex.of_d, chain_complex.of_d],
      delta FPsystem.d,
      rw [← nat_trans.comp_app, ← nat_trans.comp_app],
      congr' 1,
      apply universal_map.Tinv_comp_eval_FP2
    end },
  naturality' := begin
    intros c₁ c₂ h,
    ext n,
    dsimp only [FPsystem, Tinv_app, homological_complex.comp_f, functor.comp_map, res_app],
    rw [← functor.map_comp, ← functor.map_comp],
    refl,
  end }

def FPsystem.res [fact (r' ≤ 1)]
  (κ₁ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
  [∀ c, BD.suitable (κ₁ c)] [∀ c, BD.suitable (κ₂ c)]
  [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))]
  [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ κ₂ c n)] :
  FPsystem r' BD M κ₁ ⟶ FPsystem r' BD M κ₂ :=
{ app := λ c,
  { f := λ n, (FP2.res r' _ _ _).app M,
    comm' := begin
      rintro i j (rfl : j + 1 = i),
      dsimp only [functor.comp_obj, FPsystem],
      rw [chain_complex.of_d, chain_complex.of_d],
      delta FPsystem.d,
      rw [← nat_trans.comp_app, ← nat_trans.comp_app],
      congr' 1,
      apply universal_map.res_comp_eval_FP2
    end },
  naturality' := begin
    intros c₁ c₂ h,
    ext n,
    dsimp only [FPsystem, res_app, homological_complex.comp_f, functor.comp_map],
    rw [← functor.map_comp, ← functor.map_comp],
    refl,
  end }

end breen_deligne
