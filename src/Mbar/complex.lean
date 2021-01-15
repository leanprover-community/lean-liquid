import system_of_complexes
import locally_constant.Vhat
import Mbar.breen_deligne

import for_mathlib.CompHaus
import for_mathlib.continuous_map
import for_mathlib.free_abelian_group
import for_mathlib.add_monoid_hom

noncomputable theory

open opposite category_theory category_theory.category category_theory.limits
open_locale classical nnreal big_operators
local attribute [instance] type_pow

namespace int
/-! ### extend from nat

A helper function to define a function on the integers
by extending a function from the naturals.

We use this to define a complex indexed by `ℤ` by extending a complex indexed by `ℕ`
with zeros on negative indices.
-/

variables {X : ℤ → Sort*} (x : Π i, X i) (f : Π i : ℕ, X i)

def extend_from_nat : Π i, X i
| (n : ℕ)   := f n
| i@-[1+n]  := x i

@[simp] lemma extend_from_nat_apply_nat (n : ℕ) :
  extend_from_nat x f n = f n := rfl

@[simp] lemma extend_from_nat_apply_of_nat (n : ℕ) :
  extend_from_nat x f (int.of_nat n) = f n := rfl

@[simp] lemma extend_from_nat_apply_nat_add_one (n : ℕ) :
  extend_from_nat x f (n+1) = f (n+1) := rfl

@[simp] lemma extend_from_nat_apply_neg_succ_of_nat (n : ℕ) :
  extend_from_nat x f -[1+n] = x -[1+n] := rfl

end int

variables (V : NormedGroup) (S : Type*) (r r' c c₁ c₂ c₃ c₄ : ℝ≥0) (a : ℕ) [fintype S]

-- move this
instance fix_my_name [h1 : fact (0 < r')] [h2 : fact (r' ≤ 1)] :
  fact (c ≤ r'⁻¹ * c) :=
begin
  rw mul_comm,
  apply le_mul_inv_of_mul_le (ne_of_gt h1),
  nth_rewrite 1 ← mul_one c,
  exact mul_le_mul (le_of_eq rfl) h2 (le_of_lt h1) zero_le',
end

-- -- move this
-- instance fix_my_name₂ [h1 : fact (0 < r')] [h2 : fact (0 ≤ c)] : fact (0 ≤ c / r') :=
-- by simpa [le_div_iff h1]

-- move this
instance fix_my_name₃ [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  fact (r'⁻¹ * c₁ ≤ r'⁻¹ * c₂) :=
by { rwa [mul_le_mul_left], rw zero_lt_iff at *, apply inv_ne_zero, assumption }

/-- The functor `V-hat`, from compact Hausdorff spaces to normed groups. -/
abbreviation hat := NormedGroup.LCC.obj V

def LC_Mbar_pow [fact (0 < r')] : NormedGroup :=
(NormedGroup.LocallyConstant.obj V).obj (op $ CompHaus.of $ (Mbar_le r' S c)^a)

instance normed_with_aut_LC_Mbar_pow [fact (0 < r)] [fact (0 < r')] [normed_with_aut r V] :
  normed_with_aut r (LC_Mbar_pow V S r' c a) := by { unfold LC_Mbar_pow, apply_instance }

/-- The space `V-hat(Mbar_{r'}(S)_{≤c}^a)`. -/
def LCC_Mbar_pow [fact (0 < r')] : NormedGroup :=
(hat V).obj (op $ CompHaus.of ((Mbar_le r' S c)^a))

lemma LCC_Mbar_pow_eq [fact (0 < r')] :
  LCC_Mbar_pow V S r' c a = NormedGroup.Completion.obj (LC_Mbar_pow V S r' c a) := rfl

instance LCC_Mbar_pow_complete_space [fact (0 < r')] : complete_space (LCC_Mbar_pow V S r' c a) :=
begin
  rw LCC_Mbar_pow_eq,
  apply_instance
end

namespace LCC_Mbar_pow

-- Achtung! Achtung!
-- For technical reasons,
-- it is very important that the `[normed_with_aut r V]` instance comes last!
-- Reason: `r` is an out_param, so it should be fixed as soon as possible
-- by searching for `[normed_aut ?x_0 V]`
-- and Lean tries to fill in the typeclass assumptions from right to left.
-- Otherwise it might go on a wild goose chase for `[fact (0 < r)]`...
instance [fact (0 < r)] [fact (0 < r')] [normed_with_aut r V] :
  normed_with_aut r (LCC_Mbar_pow V S r' c a) :=
NormedGroup.normed_with_aut_LCC V _ r

lemma T_inv_eq [fact (0 < r)] [fact (0 < r')] [normed_with_aut r V] :
  (normed_with_aut.T.inv : LCC_Mbar_pow V S r' c a ⟶ LCC_Mbar_pow V S r' c a) =
    (NormedGroup.LCC.map (normed_with_aut.T.inv : V ⟶ V)).app
      (op $ CompHaus.of ((Mbar_le r' S c)^a)) :=
begin
  dsimp [LCC_Mbar_pow, LCC_Mbar_pow.normed_with_aut, NormedGroup.normed_with_aut_LCC,
    NormedGroup.normed_with_aut_Completion, NormedGroup.normed_with_aut_LocallyConstant,
    NormedGroup.LCC],
  erw [locally_constant.comap_hom_id, category.id_comp]
end

@[simp] def res₀ [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  LC_Mbar_pow V S r' c₂ a ⟶ LC_Mbar_pow V S r' c₁ a :=
(NormedGroup.LocallyConstant.obj V).map $ has_hom.hom.op $
⟨λ x, Mbar_le.cast_le ∘ x,
  continuous_pi $ λ i, (Mbar_le.continuous_cast_le r' S c₁ c₂).comp (continuous_apply i)⟩

lemma res₀_refl [fact (0 < r')] : res₀ V S r' c c a = 𝟙 _ :=
begin
  -- this can be cleaned up with some simp-lemmas
  -- will probably also make it faster
  delta res₀,
  convert category_theory.functor.map_id _ _,
  apply has_hom.hom.unop_inj,
  simp only [unop_id_op, has_hom.hom.unop_op],
  ext, dsimp, refl
end

lemma res₀_comp_res₀ [fact (0 < r')] [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ c₃)] :
  res₀ V S r' c₂ c₃ a ≫ res₀ V S r' c₁ c₂ a = res₀ V S r' c₁ c₃ a :=
by { delta res₀, rw ← functor.map_comp, refl }

def res [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  LCC_Mbar_pow V S r' c₂ a ⟶ LCC_Mbar_pow V S r' c₁ a :=
NormedGroup.Completion.map $ res₀ _ _ _ _ _ _

lemma res_refl [fact (0 < r')] : res V S r' c c a = 𝟙 _ :=
by { delta res, rw [res₀_refl], exact category_theory.functor.map_id _ _ }

@[reassoc] lemma res_comp_res [fact (0 < r')] [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ c₃)] :
  res V S r' c₂ c₃ a ≫ res V S r' c₁ c₂ a = res V S r' c₁ c₃ a :=
by {delta res, rw [← functor.map_comp, res₀_comp_res₀] }

def Tinv₀ [fact (0 < r')] :
  LC_Mbar_pow V S r' (r'⁻¹ * c) a ⟶ LC_Mbar_pow V S r' c a :=
(NormedGroup.LocallyConstant.obj V).map $ has_hom.hom.op $
⟨λ x, Mbar_le.Tinv ∘ x,
  continuous_pi $ λ i, (Mbar_le.continuous_Tinv r' S _ _).comp (continuous_apply i)⟩

def Tinv [fact (0 < r')] :
  LCC_Mbar_pow V S r' (r'⁻¹ * c) a ⟶ LCC_Mbar_pow V S r' c a :=
NormedGroup.Completion.map $ Tinv₀ _ _ _ _ _

lemma Tinv₀_res [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  Tinv₀ V S r' c₂ a ≫ res₀ V S r' c₁ c₂ a = res₀ V S r' _ _ a ≫ Tinv₀ V S r' _ a :=
by { delta Tinv₀ res₀, rw [← functor.map_comp, ← functor.map_comp], refl }

lemma Tinv_res [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  Tinv V S r' c₂ a ≫ res V S r' c₁ c₂ a = res V S r' _ _ a ≫ Tinv V S r' _ a :=
by { delta Tinv res, rw [← functor.map_comp, ← functor.map_comp, Tinv₀_res] }

open uniform_space NormedGroup

@[reassoc] lemma T_res₀ [fact (0 < r)] [fact (0 < r')] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  normed_with_aut.T.hom ≫ res₀ V S r' c₁ c₂ a = res₀ V S r' _ _ a ≫ normed_with_aut.T.hom :=
begin
  simp only [LocallyConstant_obj_map, iso.app_hom, normed_with_aut_LocallyConstant_T,
    continuous_map.coe_mk, functor.map_iso_hom, LocallyConstant_map_app, res₀, has_hom.hom.unop_op],
  ext x s,
  simp only [locally_constant.comap_hom_to_fun, function.comp_app,
    locally_constant.map_hom_to_fun, locally_constant.map_apply, coe_comp],
  repeat { erw locally_constant.coe_comap },
  refl,
  repeat
  { exact continuous_pi (λ i, (Mbar_le.continuous_cast_le r' S c₁ c₂).comp (continuous_apply i)) }
end

@[reassoc] lemma T_inv₀_res₀ [fact (0 < r)] [fact (0 < r')] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  normed_with_aut.T.inv ≫ res₀ V S r' c₁ c₂ a = res₀ V S r' _ _ a ≫ normed_with_aut.T.inv :=
by simp only [iso.inv_comp_eq, T_res₀_assoc, iso.hom_inv_id, comp_id]

@[reassoc] lemma T_res [fact (0 < r)] [fact (0 < r')] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  normed_with_aut.T.hom ≫ res V S r' c₁ c₂ a = res V S r' _ _ a ≫ normed_with_aut.T.hom :=
begin
  change NormedGroup.Completion.map _ ≫ NormedGroup.Completion.map (res₀ _ _ _ _ _ _) = _,
  change _ = NormedGroup.Completion.map (res₀ _ _ _ _ _ _) ≫ NormedGroup.Completion.map _,
  simp_rw ← category_theory.functor.map_comp,
  apply congr_arg,
  --apply T_res₀, -- doesn't work (WHY?) :-(
  exact @T_res₀ V S r r' c₁ c₂ a _ _ _ _ _,
end

@[reassoc] lemma T_inv_res [fact (0 < r)] [fact (0 < r')] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  normed_with_aut.T.inv ≫ res V S r' c₁ c₂ a = res V S r' _ _ a ≫ normed_with_aut.T.inv :=
by simp only [iso.inv_comp_eq, T_res_assoc, iso.hom_inv_id, comp_id]

end LCC_Mbar_pow

namespace breen_deligne

variable [fact (0 < r')]

variables {l m n : ℕ}

namespace basic_universal_map

def eval_Mbar_pow_aux (f : basic_universal_map m n) [f.suitable c₁ c₂] :
  CompHaus.of (Mbar_le r' S c₁ ^ m) ⟶ CompHaus.of (Mbar_le r' S c₂ ^ n) :=
{ to_fun := f.eval_Mbar_le _ _ _ _,
  continuous_to_fun := f.eval_Mbar_le_continuous _ _ _ _}

def eval_Mbar_pow (f : basic_universal_map m n) :
  (LCC_Mbar_pow V S r' c₂ n) ⟶ (LCC_Mbar_pow V S r' c₁ m) :=
if H : f.suitable c₁ c₂
then (hat V).map $ has_hom.hom.op $ @eval_Mbar_pow_aux S r' c₁ c₂ _ _ _ _ f H
else 0

lemma eval_Mbar_pow_def (f : basic_universal_map m n) [f.suitable c₁ c₂] :
  f.eval_Mbar_pow V S r' c₁ c₂ =
    (hat V).map (has_hom.hom.op $ ⟨f.eval_Mbar_le _ _ _ _, f.eval_Mbar_le_continuous _ _ _ _⟩) :=
by { rw [eval_Mbar_pow, dif_pos], refl }

lemma eval_Mbar_pow_comp (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (g.comp f).eval_Mbar_pow V S r' c₁ c₃ =
  g.eval_Mbar_pow V S r' c₂ c₃ ≫ f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  haveI : (g.comp f).suitable c₁ c₃ := suitable_comp c₂,
  simp only [eval_Mbar_pow_def],
  rw [← category_theory.functor.map_comp, ← op_comp],
  congr' 2,
  simpa [eval_Mbar_le_comp r' S _ c₂],
end

lemma eval_Mbar_pow_comp_res (f : basic_universal_map m n)
  [f.suitable c₁ c₂] [f.suitable c₃ c₄] [fact (c₁ ≤ c₃)] [fact (c₂ ≤ c₄)] :
  f.eval_Mbar_pow V S r' c₃ c₄ ≫ LCC_Mbar_pow.res V S r' c₁ c₃ m =
  LCC_Mbar_pow.res V S r' c₂ c₄ n ≫ f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  rw [eval_Mbar_pow_def, eval_Mbar_pow_def, NormedGroup.LCC_obj_map', NormedGroup.LCC_obj_map'],
  delta LCC_Mbar_pow.res LCC_Mbar_pow.res₀,
  rw [← functor.map_comp, ← functor.map_comp, ← functor.map_comp,
      ← functor.map_comp, ← op_comp, ← op_comp],
  congr' 3,
  ext x i s k,
  show (f.eval_Mbar_le r' S c₃ c₄ ∘ (function.comp Mbar_le.cast_le)) x i s k =
    ((function.comp Mbar_le.cast_le) ∘ (f.eval_Mbar_le r' S c₁ c₂)) x i s k,
  dsimp [function.comp],
  simp only [Mbar_le.coe_cast_le]
end

lemma eval_Mbar_pow_comp_Tinv (f : basic_universal_map m n) [f.suitable c₁ c₂] :
  f.eval_Mbar_pow V S r' (r'⁻¹ * c₁) (r'⁻¹ * c₂) ≫ LCC_Mbar_pow.Tinv V S r' c₁ m =
    LCC_Mbar_pow.Tinv V S r' c₂ n ≫ f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  rw [eval_Mbar_pow_def, eval_Mbar_pow_def, NormedGroup.LCC_obj_map', NormedGroup.LCC_obj_map'],
  delta LCC_Mbar_pow.Tinv LCC_Mbar_pow.Tinv₀,
  rw [← functor.map_comp, ← functor.map_comp, ← functor.map_comp,
      ← functor.map_comp, ← op_comp, ← op_comp],
  congr' 3,
  ext x j s k, dsimp at *,
  show (f.eval_Mbar_le r' S _ _ ∘ (function.comp Mbar_le.Tinv)) x j s k =
    ((function.comp Mbar_le.Tinv) ∘ (f.eval_Mbar_le r' S c₁ c₂)) x j s k,
  dsimp [function.comp, Mbar.Tinv],
  cases k,
  { simp only [Mbar.coeff_zero] },
  { simp only [Mbar.Tinv_aux_succ, add_monoid_hom.coe_mk', eval_Mbar_le_apply, Mbar.coe_smul,
      Mbar.coe_mk, Mbar_le.coe_coe_to_fun, eval_png_apply, Mbar.coe_sum, fintype.sum_apply,
      pi.smul_apply, Mbar.Tinv_succ],
    refl }
end

lemma eval_Mbar_pow_comp_T_inv (f : basic_universal_map m n) [f.suitable c₁ c₂]
  [fact (0 < r)] [normed_with_aut r V] :
  f.eval_Mbar_pow V S r' c₁ c₂ ≫ normed_with_aut.T.inv =
    normed_with_aut.T.inv ≫ f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  rw [LCC_Mbar_pow.T_inv_eq, LCC_Mbar_pow.T_inv_eq, eval_Mbar_pow_def],
  apply nat_trans.naturality
end

end basic_universal_map

namespace universal_map

open free_abelian_group

/-- A univeral map `f` is `suitable c₁ c₂` if all of the matrices `g`
occuring in the formal sum `f` satisfy `g.suitable c₁ c₂`.
This definition is tailored in such a way that we get a sensible
`(LCC_Mbar_pow V S r' c₂ n) ⟶ (LCC_Mbar_pow V S r' c₁ m)`
if `f.suitable c₁ c₂`.

See Lemma 9.11 of [Analytic]. -/
def suitable (c₁ c₂ : ℝ≥0) (f : universal_map m n) : Prop :=
∀ g ∈ f.support, basic_universal_map.suitable g c₁ c₂

attribute [class] suitable

lemma suitable_of_mem_support (f : universal_map m n) (c₁ c₂ : ℝ≥0)
  (g : basic_universal_map m n) (hg : g ∈ f.support) [h : f.suitable c₁ c₂] :
  g.suitable c₁ c₂ :=
h g hg

lemma suitable_free_predicate (c₁ c₂ : ℝ≥0) :
  free_predicate (@suitable m n c₁ c₂) :=
by { intro x, simp only [suitable, forall_eq, finset.mem_singleton, support_of] }

lemma suitable_congr (f g : universal_map m n) (c₁ c₂ : ℝ≥0) (h : f = g) :
  f.suitable c₁ c₂ ↔ g.suitable c₁ c₂ :=
by subst h

end universal_map

namespace basic_universal_map
open free_abelian_group

instance suitable_of (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) [f.suitable c₁ c₂] :
  universal_map.suitable c₁ c₂ (of f) :=
begin
  intros g hg,
  rw [support_of, finset.mem_singleton] at hg,
  rwa hg
end

instance suitable_of_suitable_of (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0)
  [h : universal_map.suitable c₁ c₂ (of f)] :
  f.suitable c₁ c₂ :=
h f $ by simp only [finset.mem_singleton, support_of]

end basic_universal_map

namespace universal_map
open free_abelian_group

@[simp] lemma suitable_of_iff (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (of f) ↔ f.suitable c₁ c₂ :=
⟨by {introI h, apply_instance}, by {introI h, apply_instance}⟩

instance suitable_zero : (0 : universal_map m n).suitable c₁ c₂ :=
(suitable_free_predicate c₁ c₂).zero

instance suitable_neg (f : universal_map m n) (c₁ c₂ : ℝ≥0) [h : f.suitable c₁ c₂] :
  suitable c₁ c₂ (-f) :=
(suitable_free_predicate c₁ c₂).neg h

@[simp] lemma suitable_neg_iff (f : universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (-f) ↔ f.suitable c₁ c₂ :=
(suitable_free_predicate c₁ c₂).neg_iff

instance suitable_add {f g : universal_map m n} {c₁ c₂ : ℝ≥0}
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₁ c₂] :
  suitable c₁ c₂ (f + g) :=
(suitable_free_predicate c₁ c₂).add hf hg

lemma suitable_smul_iff (k : ℤ) (hk : k ≠ 0) (f : universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (k • f) ↔ f.suitable c₁ c₂ :=
(suitable_free_predicate c₁ c₂).smul_iff k hk

instance suitable_of_mul_left (f : universal_map m n) [h : f.suitable c₁ c₂] :
  f.suitable (c * c₁) (c * c₂) :=
λ g hg, @basic_universal_map.suitable_of_mul_left _ _ _ _ _ _ (h g hg)

-- this cannot be an instance, because c₂ cannot be inferred
lemma suitable.comp {g : universal_map m n} {f : universal_map l m} {c₁ : ℝ≥0} (c₂ : ℝ≥0)
  {c₃ : ℝ≥0} [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (comp g f).suitable c₁ c₃ :=
begin
  apply free_abelian_group.induction_on_free_predicate
    (suitable c₂ c₃) (suitable_free_predicate c₂ c₃) g hg; unfreezingI { clear_dependent g },
  { simpa only [pi.zero_apply, add_monoid_hom.coe_zero, add_monoid_hom.map_zero]
      using breen_deligne.universal_map.suitable_zero _ _ },
  { intros g hg,
    apply free_abelian_group.induction_on_free_predicate
      (suitable c₁ c₂) (suitable_free_predicate c₁ c₂) f hf; unfreezingI { clear_dependent f },
      { simp only [add_monoid_hom.map_zero], apply_instance },
      { intros f hf,
        rw comp_of,
        rw suitable_of_iff at hf hg ⊢,
        resetI,
        exact breen_deligne.basic_universal_map.suitable_comp c₂ },
      { intros g hg H, simpa only [add_monoid_hom.map_neg, suitable_neg_iff] },
      { intros g₁ g₂ hg₁ hg₂ H₁ H₂,
        simp only [add_monoid_hom.map_add],
        resetI, apply_instance } },
  { intros f hf H,
    simpa only [pi.neg_apply, add_monoid_hom.map_neg, suitable_neg_iff, add_monoid_hom.coe_neg] },
  { intros f₁ f₂ hf₁ hf₂ H₁ H₂,
    simp only [add_monoid_hom.coe_add, add_monoid_hom.map_add, pi.add_apply],
    resetI, apply_instance }
end

def eval_Mbar_pow {m n : ℕ} (f : universal_map m n) :
  (LCC_Mbar_pow V S r' c₂ n) ⟶ (LCC_Mbar_pow V S r' c₁ m) :=
if H : (f.suitable c₁ c₂)
then by exactI
  ∑ g in f.support, coeff g f • (g.eval_Mbar_pow V S r' c₁ c₂)
else 0

lemma eval_Mbar_pow_def {m n : ℕ} (f : universal_map m n) [H : f.suitable c₁ c₂] :
  f.eval_Mbar_pow V S r' c₁ c₂ = ∑ g in f.support, coeff g f • (g.eval_Mbar_pow V S r' c₁ c₂) :=
by { rw [eval_Mbar_pow, dif_pos], exact H }

@[simp] lemma eval_Mbar_pow_of (f : basic_universal_map m n) [f.suitable c₁ c₂] :
  eval_Mbar_pow V S r' c₁ c₂ (of f) = f.eval_Mbar_pow V S r' c₁ c₂ :=
by simp only [eval_Mbar_pow_def, support_of, coeff_of_self, one_smul, finset.sum_singleton]

@[simp] lemma eval_Mbar_pow_zero :
  (0 : universal_map m n).eval_Mbar_pow V S r' c₁ c₂ = 0 :=
by rw [eval_Mbar_pow_def, support_zero, finset.sum_empty]

@[simp] lemma eval_Mbar_pow_neg (f : universal_map m n) :
  eval_Mbar_pow V S r' c₁ c₂ (-f) = -f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  rw eval_Mbar_pow,
  split_ifs,
  { rw suitable_neg_iff at h,
    rw [eval_Mbar_pow, dif_pos h],
    simp only [add_monoid_hom.map_neg, finset.sum_neg_distrib, neg_smul, support_neg] },
  { rw suitable_neg_iff at h,
    rw [eval_Mbar_pow, dif_neg h, neg_zero] }
end

lemma eval_Mbar_pow_add (f g : universal_map m n)
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₁ c₂] :
  eval_Mbar_pow V S r' c₁ c₂ (f + g) =
    f.eval_Mbar_pow V S r' c₁ c₂ + g.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  simp only [eval_Mbar_pow_def],
  rw finset.sum_subset (support_add f g), -- two goals
  simp only [add_monoid_hom.map_add _ f g, add_smul],
  convert finset.sum_add_distrib using 2, -- three goals
  apply finset.sum_subset (finset.subset_union_left _ _), swap,
  apply finset.sum_subset (finset.subset_union_right _ _),
  all_goals { rintros x - h, rw not_mem_support_iff at h, simp [h] },
end

lemma eval_Mbar_pow_comp_of (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  eval_Mbar_pow V S r' c₁ c₃ ((comp (of g)) (of f)) =
    eval_Mbar_pow V S r' c₂ c₃ (of g) ≫ eval_Mbar_pow V S r' c₁ c₂ (of f) :=
begin
  haveI hfg : (g.comp f).suitable c₁ c₃ := basic_universal_map.suitable_comp c₂,--hg.comp hf,
  simp only [comp_of, eval_Mbar_pow_of],
  rw ← basic_universal_map.eval_Mbar_pow_comp,
end

lemma eval_Mbar_pow_comp (g : universal_map m n) (f : universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (comp g f).eval_Mbar_pow V S r' c₁ c₃ =
    g.eval_Mbar_pow V S r' c₂ c₃ ≫ f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  unfreezingI { revert hf },
  apply free_abelian_group.induction_on_free_predicate
    (suitable c₂ c₃) (suitable_free_predicate c₂ c₃) g hg; unfreezingI { clear_dependent g },
  { intros h₂,
    simp only [eval_Mbar_pow_zero, zero_comp, pi.zero_apply,
      add_monoid_hom.coe_zero, add_monoid_hom.map_zero] },
  { intros g hg hf,
    -- now do another nested induction on `f`
    apply free_abelian_group.induction_on_free_predicate
      (suitable c₁ c₂) (suitable_free_predicate c₁ c₂) f hf; unfreezingI { clear_dependent f },
    { simp only [eval_Mbar_pow_zero, comp_zero, add_monoid_hom.map_zero] },
    { intros f hf,
      rw suitable_of_iff at hf,
      resetI,
      apply eval_Mbar_pow_comp_of },
    { intros f hf IH,
      show _ = normed_group_hom.comp_hom _ _,
      simp only [IH, pi.neg_apply, add_monoid_hom.map_neg, eval_Mbar_pow_neg,
        add_monoid_hom.coe_neg, neg_inj],
      refl },
    { rintros (f₁ : universal_map l m) (f₂ : universal_map l m) hf₁ hf₂ IH₁ IH₂, resetI,
      haveI Hg₁f : (comp (of g) f₁).suitable c₁ c₃ := suitable.comp c₂,
      haveI Hg₂f : (comp (of g) f₂).suitable c₁ c₃ := suitable.comp c₂,
      simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply, eval_Mbar_pow_add, IH₁, IH₂],
      show _ = normed_group_hom.comp_hom _ _,
      simpa [add_monoid_hom.map_add] } },
  { intros g hg IH hf, resetI, specialize IH,
    show _ = normed_group_hom.comp_hom _ _,
    simp only [IH, pi.neg_apply, add_monoid_hom.map_neg, eval_Mbar_pow_neg, add_monoid_hom.coe_neg,
      neg_inj],
    refl },
  { rintros (g₁ : universal_map m n) (g₂ : universal_map m n) hg₁ hg₂ IH₁ IH₂ hf, resetI,
    haveI Hg₁f : (comp g₁ f).suitable c₁ c₃ := suitable.comp c₂,
    haveI Hg₂f : (comp g₂ f).suitable c₁ c₃ := suitable.comp c₂,
    simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply, eval_Mbar_pow_add, IH₁, IH₂],
    show _ = normed_group_hom.comp_hom _ _,
    simpa [add_monoid_hom.map_add] }
end

@[simp] lemma eval_Mbar_pow_smul (k : ℤ) (f : universal_map m n)
  [f.suitable c₁ c₂] [(k • f).suitable c₁ c₂] :
  eval_Mbar_pow V S r' c₁ c₂ (k • f) = k • f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  by_cases hk : k = 0,
  { simp only [hk, eval_Mbar_pow_zero, zero_smul] },
  simp only [eval_Mbar_pow_def, support_smul k hk],
  rw finset.smul_sum,
  apply finset.sum_congr rfl,
  rintro g hg,
  rw ← smul_assoc,
  simp only [← gsmul_eq_smul k, ← add_monoid_hom.map_gsmul]
end

@[reassoc] lemma eval_Mbar_pow_comp_res (f : universal_map m n)
  [f.suitable c₁ c₂] [f.suitable c₃ c₄] [fact (c₁ ≤ c₃)] [fact (c₂ ≤ c₄)] :
  f.eval_Mbar_pow V S r' c₃ c₄ ≫ LCC_Mbar_pow.res V S r' c₁ c₃ m =
  LCC_Mbar_pow.res V S r' c₂ c₄ n ≫ f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  show normed_group_hom.comp_hom _ _ = normed_group_hom.comp_hom _ _,
  rw [eval_Mbar_pow_def, add_monoid_hom.map_sum,
      eval_Mbar_pow_def, add_monoid_hom.map_sum,
      add_monoid_hom.sum_apply],
  apply finset.sum_congr rfl,
  rintro g hg,
  rw [← gsmul_eq_smul, add_monoid_hom.map_gsmul,
      ← gsmul_eq_smul, add_monoid_hom.map_gsmul,
      add_monoid_hom.gsmul_apply],
  haveI : g.suitable c₁ c₂ := f.suitable_of_mem_support c₁ c₂ g hg,
  haveI : g.suitable c₃ c₄ := f.suitable_of_mem_support c₃ c₄ g hg,
  have := basic_universal_map.eval_Mbar_pow_comp_res V S r' c₁ c₂ c₃ c₄ g,
  change normed_group_hom.comp_hom _ _ = normed_group_hom.comp_hom _ _ at this,
  rw this
end

@[reassoc] lemma eval_Mbar_pow_comp_Tinv (f : universal_map m n) [f.suitable c₁ c₂] :
  eval_Mbar_pow V S r' (r'⁻¹ * c₁) (r'⁻¹ * c₂) f ≫ LCC_Mbar_pow.Tinv V S r' c₁ m =
    LCC_Mbar_pow.Tinv V S r' c₂ n ≫ eval_Mbar_pow V S r' c₁ c₂ f :=
begin
  show normed_group_hom.comp_hom _ _ = normed_group_hom.comp_hom _ _,
  rw [eval_Mbar_pow_def, eval_Mbar_pow_def, add_monoid_hom.map_sum, add_monoid_hom.map_sum,
      add_monoid_hom.sum_apply],
  apply finset.sum_congr rfl,
  intros g hg,
  rw [← gsmul_eq_smul, ← gsmul_eq_smul, add_monoid_hom.map_gsmul, add_monoid_hom.map_gsmul,
      add_monoid_hom.gsmul_apply],
  congr' 1,
  haveI : g.suitable c₁ c₂ := suitable_of_mem_support f c₁ c₂ g hg,
  exact g.eval_Mbar_pow_comp_Tinv V S r' _ _
end

@[reassoc] lemma eval_Mbar_pow_comp_T_inv (f : universal_map m n) [f.suitable c₁ c₂]
  [fact (0 < r)] [normed_with_aut r V] :
  f.eval_Mbar_pow V S r' c₁ c₂ ≫ normed_with_aut.T.inv =
    normed_with_aut.T.inv ≫ f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  show normed_group_hom.comp_hom _ _ = normed_group_hom.comp_hom _ _,
  rw [eval_Mbar_pow_def, add_monoid_hom.map_sum, add_monoid_hom.map_sum,
      add_monoid_hom.sum_apply],
  apply finset.sum_congr rfl,
  intros g hg,
  rw [← gsmul_eq_smul, add_monoid_hom.map_gsmul, add_monoid_hom.map_gsmul,
      add_monoid_hom.gsmul_apply],
  congr' 1,
  haveI : g.suitable c₁ c₂ := suitable_of_mem_support f c₁ c₂ g hg,
  exact g.eval_Mbar_pow_comp_T_inv V S r r' _ _
end

-- move this
instance le_of_mul_right [fact (c₁ ≤ c₂)] : fact ((c₁ * c₃) ≤ (c₂ * c₃)) :=
mul_le_mul' ‹_› le_rfl

end universal_map

namespace package

class suitable (BD : package) (c' : ℕ → ℝ≥0) : Prop :=
(universal_suitable : ∀ i, (BD.map i).suitable (c' (i+1)) (c' i))

variables (BD : package) (c' : ℕ → ℝ≥0) (i : ℕ) [BD.suitable c']

instance basic_suitable_of_suitable : ((BD.map i).suitable (c' (i+1)) (c' i)) :=
suitable.universal_suitable i

instance suitable_of_suitable :
  ((universal_map.comp (BD.map i) (BD.map (i+1))).suitable (c' (i+2)) (c' i)) :=
universal_map.suitable.comp (c' (i + 1))

end package

end breen_deligne
