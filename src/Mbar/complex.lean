import system_of_complexes
import locally_constant.Vhat
import Mbar.breen_deligne

import for_mathlib.CompHaus
import for_mathlib.continuous_map
import for_mathlib.free_abelian_group
import for_mathlib.add_monoid_hom

noncomputable theory

open opposite category_theory category_theory.limits
open_locale nnreal big_operators
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

variables (V : NormedGroup) (S : Type*) (r r' c c' c₁ c₂ c₃ c₄ : ℝ≥0) (a : ℕ) [fintype S]

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

-- Achtung! Achtung! It is very important that the `[normed_with_aut r V]` instance comes last!
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

def res [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  LCC_Mbar_pow V S r' c₂ a ⟶ LCC_Mbar_pow V S r' c₁ a :=
NormedGroup.Completion.map $ res₀ _ _ _ _ _ _

lemma res₀_comp_res₀ [fact (0 < r')] [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ c₃)] :
  res₀ V S r' c₂ c₃ a ≫ res₀ V S r' c₁ c₂ a = res₀ V S r' c₁ c₃ a :=
by { delta res₀, rw ← functor.map_comp, refl }

lemma res_comp_res [fact (0 < r')] [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ c₃)] :
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

lemma T_res₀ [fact (0 < r)] [fact (0 < r')] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
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

lemma T_inv₀_res₀ [fact (0 < r)] [fact (0 < r')] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  normed_with_aut.T.inv ≫ res₀ V S r' c₁ c₂ a = res₀ V S r' _ _ a ≫ normed_with_aut.T.inv :=
begin
  simp only [iso.inv_comp_eq],
  symmetry,
  rw ← category.assoc,
  simp only [iso.comp_inv_eq],
  apply T_res₀,
end

lemma T_res [fact (0 < r)] [fact (0 < r')] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  normed_with_aut.T.hom ≫ res V S r' c₁ c₂ a = res V S r' _ _ a ≫ normed_with_aut.T.hom :=
begin
  change NormedGroup.Completion.map _ ≫ NormedGroup.Completion.map (res₀ _ _ _ _ _ _) = _,
  change _ = NormedGroup.Completion.map (res₀ _ _ _ _ _ _) ≫ NormedGroup.Completion.map _,
  simp_rw ← category_theory.functor.map_comp,
  apply congr_arg,
  --apply T_res₀, -- doesn't work (WHY?) :-(
  exact @T_res₀ V S r r' c₁ c₂ a _ _ _ _ _,
end

lemma T_inv_res [fact (0 < r)] [fact (0 < r')] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  normed_with_aut.T.inv ≫ res V S r' c₁ c₂ a = res V S r' _ _ a ≫ normed_with_aut.T.inv :=
begin
  simp only [iso.inv_comp_eq],
  symmetry,
  rw ← category.assoc,
  simp only [iso.comp_inv_eq],
  apply T_res,
end

end LCC_Mbar_pow

namespace breen_deligne

variable [fact (0 < r')]

variables {l m n : ℕ}

namespace basic_universal_map

def eval_Mbar_pow (f : basic_universal_map m n) [fact (f.suitable c' c)] :
  (LCC_Mbar_pow V S r' c n) ⟶ (LCC_Mbar_pow V S r' c' m) :=
(hat V).map $ has_hom.hom.op $ ⟨f.eval_Mbar_le _ _ _ _, f.eval_Mbar_le_continuous _ _ _ _⟩

local attribute [instance] fact_zero_suitable

-- WARNING: this lemma is false

-- lemma eval_Mbar_pow_zero :
--   (0 : basic_universal_map m n).eval_Mbar_pow V S r' c c' = 0 :=
-- begin
--   dsimp [eval_Mbar_pow],
--   convert NormedGroup.Completion.map_zero _ _ using 1,
--   ext1 v,
--   rw NormedGroup.LCC_obj_map V,
--   simp only [continuous_map.coe_mk, pi.zero_apply, normed_group_hom.coe_zero, has_hom.hom.unop_op,
--     eval_Mbar_le_zero],
--   -- the following is ugly, need to clean up
--   dsimp at *,
--   congr,
--   rw locally_constant.comap_const 0, swap 3, { exact 0 },
--   { ext f x, dsimp, show f 0 = 0,
--     /- This sorry is false )-; -/
--     sorry },
--   { intro, refl }
-- end

lemma eval_Mbar_pow_comp (f : basic_universal_map m n) (g : basic_universal_map l m)
  [fact (f.suitable c₂ c₁)] [fact (g.suitable c₃ c₂)] [fact ((f.comp g).suitable c₃ c₁)] :
  (f.comp g).eval_Mbar_pow V S r' c₁ c₃ =
  f.eval_Mbar_pow V S r' c₁ c₂ ≫ g.eval_Mbar_pow V S r' c₂ c₃ :=
begin
  dsimp [eval_Mbar_pow],
  rw [← category_theory.functor.map_comp, ← op_comp],
  congr' 2,
  ext1 j,
  dsimp,
  rw eval_Mbar_le_comp r' S c₁ c₂ c₃,
  refl
end

end basic_universal_map

namespace universal_map

open free_abelian_group

/-- Addition goes from `Mbar r' S c` to `Mbar r' S c'` for suitable `c'`.
This predicate says what *suitable* means for universal maps.
See Lemma 9.11 of [Analytic]. -/
def suitable (c₁ c₂ : ℝ≥0) (f : universal_map m n) : Prop :=
∀ g ∈ f.support, basic_universal_map.suitable g c₁ c₂

instance suitable_of_mem_support (f : universal_map m n) (c₁ c₂ : ℝ≥0) (g : {g // g ∈ f.support})
  [h : fact (f.suitable c₁ c₂)] :
  fact (basic_universal_map.suitable ↑g c₁ c₂) :=
h g.1 g.2

instance suitable_of (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) [h : fact (f.suitable c₁ c₂)] :
  fact (suitable c₁ c₂ (of f)) :=
begin
  intros g hg,
  rw [support_of, finset.mem_singleton] at hg,
  rwa hg
end

lemma suitable_free_predicate (c₁ c₂ : ℝ≥0) :
  free_predicate (@suitable m n c₁ c₂) :=
by { intro x, simp only [suitable, forall_eq, finset.mem_singleton, support_of] }

lemma suitable_congr (f g : universal_map m n) (c₁ c₂ : ℝ≥0) (h : f = g) :
  f.suitable c₁ c₂ ↔ g.suitable c₁ c₂ :=
by subst h

lemma suitable_of_suitable_of (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0)
  [h : fact (suitable c₁ c₂ (of f))] :
  fact (f.suitable c₁ c₂) :=
h f $ by simp only [finset.mem_singleton, support_of]

lemma suitable_of_iff (f : basic_universal_map m n) (c₁ c₂ : ℝ≥0) :
  fact (suitable c₁ c₂ (of f)) ↔ fact (f.suitable c₁ c₂) :=
⟨by introsI h; apply suitable_of_suitable_of, by introsI h; apply_instance⟩

instance suitable_neg (f : universal_map m n) (c₁ c₂ : ℝ≥0) [h : fact (f.suitable c₁ c₂)] :
  fact (suitable c₁ c₂ (-f)) :=
by { intros g hg, rw [support_neg] at hg, exact h g hg }

lemma suitable_smul_iff (k : ℤ) (hk : k ≠ 0) (f : universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (k • f) ↔ f.suitable c₁ c₂ :=
by { apply forall_congr, intros g, rw support_smul k hk }

lemma suitable_neg_iff (f : universal_map m n) (c₁ c₂ : ℝ≥0) :
  suitable c₁ c₂ (-f) ↔ f.suitable c₁ c₂ :=
⟨by { intro h, rw ← neg_neg f, exact @universal_map.suitable_neg _ _ _ c₁ c₂ h },
 by { intro h, exact @universal_map.suitable_neg _ _ _ c₁ c₂ h }⟩

lemma suitable_comp (f : universal_map m n) (g : universal_map l m)
  (hf : f.suitable c₂ c₁) (hg : g.suitable c₃ c₂) :
  (comp f g).suitable c₃ c₁ :=

lemma suitable_of_suitable_add_of₁ (g : universal_map m n) (i : ℤ) (hi : i ≠ 0)
  (f : basic_universal_map m n) (hfg : f ∉ g.support) (h : suitable c₁ c₂ (g + i • of f)) :
  g.suitable c₁ c₂ :=
sorry

lemma suitable_of_suitable_add_of₂ (g : universal_map m n) (i : ℤ) (hi : i ≠ 0)
  (f : basic_universal_map m n) (hfg : f ∉ g.support) (h : suitable c₁ c₂ (g + i • of f)) :
  f.suitable c₁ c₂ :=
sorry

lemma zero_suitable : fact ((0 : universal_map m n).suitable c' c) :=
λ g hg,
by { simp only [support_zero, finset.not_mem_empty] at hg, exact hg.elim }

local attribute [instance] zero_suitable

section aux

open_locale classical

def eval_Mbar_pow {m n : ℕ} (f : universal_map m n) :
  (LCC_Mbar_pow V S r' c₁ n) ⟶ (LCC_Mbar_pow V S r' c₂ m) :=
if H : (f.suitable c₂ c₁)
then by have H' : fact (f.suitable c₂ c₁) := H; exactI
∑ g : {g // g ∈ f.support}, coeff ↑g f •
                              (basic_universal_map.eval_Mbar_pow V S r' c₁ c₂ ↑g)
else 0

lemma eval_Mbar_pow_def {m n : ℕ} (f : universal_map m n) [H : fact (f.suitable c₂ c₁)] :
  f.eval_Mbar_pow V S r' c₁ c₂ =
  ∑ g : {g // g ∈ f.support}, coeff ↑g f •
                              (basic_universal_map.eval_Mbar_pow V S r' c₁ c₂ ↑g) :=
by rw [eval_Mbar_pow, dif_pos]

@[simp] lemma eval_Mbar_pow_zero :
  (0 : universal_map m n).eval_Mbar_pow V S r' c c' = 0 :=
begin
  rw [eval_Mbar_pow],
  split_ifs, swap, { refl }, resetI,
  rw finset.sum_eq_zero,
  rintro ⟨g, hg⟩,
  simp only [support_zero, finset.not_mem_empty] at hg,
  exact hg.elim
end

@[simp] lemma eval_Mbar_pow_neg (f : universal_map m n) :
  eval_Mbar_pow V S r' c₁ c₂ (-f) = -f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  rw eval_Mbar_pow,
  split_ifs,
  { rw suitable_neg_iff at h,
    rw [eval_Mbar_pow, dif_pos h],
    simp only [eval_Mbar_pow, add_monoid_hom.map_neg, finset.sum_neg_distrib, neg_smul, neg_inj],
    apply finset.sum_bij (λ g hg, _),
    swap 5, { refine ⟨↑g, _⟩, simpa only [support_neg] using g.2 },
    { intros, exact finset.mem_univ _ },
    { intros, refl },
    { intros _ _ _ _ H, simp only [subtype.ext_iff, subtype.coe_mk] at H ⊢, exact H },
    { intros g hg,
      refine ⟨⟨↑g, _⟩, finset.mem_univ _, _⟩, { simpa only [support_neg] using g.2 },
      ext, refl } },
  { rw suitable_neg_iff at h,
    rw [eval_Mbar_pow, dif_neg h, neg_zero] }
end

lemma eval_Mbar_pow_comp (f : universal_map m n) (g : universal_map l m)
  [h₁ : fact (f.suitable c₂ c₁)] [h₂ : fact (g.suitable c₃ c₂)] :
  (universal_map.comp f g).eval_Mbar_pow V S r' c₁ c₃ =
    f.eval_Mbar_pow V S r' c₁ c₂ ≫ g.eval_Mbar_pow V S r' c₂ c₃ :=
begin
  unfreezingI { revert h₂ },
  apply free_abelian_group.induction_on_free_predicate
    (suitable c₂ c₁) (suitable_free_predicate c₂ c₁) f h₁; unfreezingI { clear_dependent f },
  { intros h₂,
    simp only [eval_Mbar_pow_zero, zero_comp, pi.zero_apply,
      add_monoid_hom.coe_zero, add_monoid_hom.map_zero] },
  { intros f hf hg, sorry },
  { intros f hf IH hg, resetI, specialize IH,
    show _ = normed_group_hom.comp_hom _ _,
    simp only [IH, pi.neg_apply, add_monoid_hom.map_neg, eval_Mbar_pow_neg, add_monoid_hom.coe_neg,
      neg_inj],
    refl },
  { intros f₁ f₂ hf₁ hf₂ IH₁ IH₂ hg, resetI, specialize IH₁, specialize IH₂, sorry }
end

end aux

def eval_Mbar_pow {m n : ℕ} (f : universal_map m n) [fact (f.suitable c₂ c₁)] :
  (LCC_Mbar_pow V S r' c₁ n) ⟶ (LCC_Mbar_pow V S r' c₂ m) :=
∑ g : {g // g ∈ f.support}, coeff ↑g f •
                              (basic_universal_map.eval_Mbar_pow V S r' c₁ c₂ ↑g)


@[simp] lemma eval_Mbar_pow_of (f : basic_universal_map m n) [fact (f.suitable c₂ c₁)] :
  eval_Mbar_pow V S r' c₁ c₂ (of f) = f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  rw [eval_Mbar_pow, finset.sum_eq_single],
  swap 4, { refine ⟨f, _⟩, simp only [finset.mem_singleton, support_of] },
  { simp only [coeff_of_self, one_smul, subtype.coe_mk] },
  { rintro ⟨g, hg⟩ H H',
    simp only [finset.mem_singleton, support_of] at hg,
    simp only [ne.def] at H',
    exact (H' hg).elim },
  { intro h, exact (h (finset.mem_univ _)).elim }
end

lemma eval_Mbar_pow_comp_of (g : basic_universal_map l m) (f : basic_universal_map m n)
  [h₁ : fact (f.suitable c₂ c₁)]
  [h₂ : fact (g.suitable c₃ c₂)]
  [h₃ : fact (((comp (of f)) (of g)).suitable c₃ c₁)] :
  eval_Mbar_pow V S r' c₁ c₃ ((comp (of f)) (of g)) =
    eval_Mbar_pow V S r' c₁ c₂ (of f) ≫ eval_Mbar_pow V S r' c₂ c₃ (of g) :=
begin
  have := h₃ (f.comp g),
  simp only [comp_of, support_of, finset.mem_singleton_self, true_implies_iff] at ⊢ this,
  haveI : fact ((f.comp g).suitable c₃ c₁) := this,
  simp only [eval_Mbar_pow_of],
  rw ← basic_universal_map.eval_Mbar_pow_comp
end

@[simp] lemma eval_Mbar_pow_neg (f : universal_map m n) [fact (f.suitable c₂ c₁)] :
  eval_Mbar_pow V S r' c₁ c₂ (-f) = -f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  simp only [eval_Mbar_pow, add_monoid_hom.map_neg, finset.sum_neg_distrib, neg_smul, neg_inj],
  apply finset.sum_bij (λ g hg, _),
  swap 5, { refine ⟨↑g, _⟩, simpa only [support_neg] using g.2 },
  { intros, exact finset.mem_univ _ },
  { intros, refl },
  { intros _ _ _ _ H, simp only [subtype.ext_iff, subtype.coe_mk] at H ⊢, exact H },
  { intros g hg,
    refine ⟨⟨↑g, _⟩, finset.mem_univ _, _⟩, { simpa only [support_neg] using g.2 },
    ext, refl }
end

@[simp] lemma eval_Mbar_pow_smul (k : ℤ) (f : universal_map m n)
  [fact (f.suitable c₂ c₁)] [fact ((k • f).suitable c₂ c₁)] :
  eval_Mbar_pow V S r' c₁ c₂ (k • f) = k • f.eval_Mbar_pow V S r' c₁ c₂ :=
begin
  by_cases hk : k = 0,
  { simp only [hk, eval_Mbar_pow_zero, zero_smul] },
  simp only [eval_Mbar_pow],
  rw finset.smul_sum,
  let e : {g // g ∈ f.support} ≃ {g // g ∈ (k • f).support} :=
  equiv.subtype_congr_prop (by { ext, rw support_smul k hk }),
  rw ← e.sum_comp,
  apply fintype.sum_congr,
  rintro ⟨g, hg⟩,
  rw ← smul_assoc,
  congr' 1,
  simp only [← gsmul_eq_smul k, ← add_monoid_hom.map_gsmul],
  refl
end

@[simp] lemma eval_Mbar_pow_add_smul_of (f : universal_map m n) (k : ℤ) (hk : k ≠ 0)
  (g : basic_universal_map m n) (hfg : g ∉ f.support)
  [fact (f.suitable c₂ c₁)] [fact (g.suitable c₂ c₁)] [fact ((f + k • of g).suitable c₂ c₁)] :
  (f + k • of g).eval_Mbar_pow V S r' c₁ c₂ =
    (f.eval_Mbar_pow V S r' c₁ c₂) + k • (g.eval_Mbar_pow V S r' c₁ c₂) :=
begin
  simp only [eval_Mbar_pow, add_monoid_hom.map_add, add_smul, finset.sum_add_distrib],
  congr' 1,
  { apply finset.sum_bij_ne_zero; sorry },
  { sorry }
end

lemma eval_Mbar_pow_comp_smul_of (j i : ℤ) (hj : j ≠ 0) (hi : i ≠ 0)
  (g : basic_universal_map l m) (f : basic_universal_map m n)
  [h₁ : fact (suitable c₂ c₁ (i • of f))]
  [h₂ : fact (suitable c₃ c₂ (j • of g))]
  [h₃ : fact (((comp (i • of f)) (j • of g)).suitable c₃ c₁)] :
  eval_Mbar_pow V S r' c₁ c₃ ((comp (i • of f)) (j • of g)) =
    eval_Mbar_pow V S r' c₁ c₂ (i • of f) ≫ eval_Mbar_pow V S r' c₂ c₃ (j • of g) :=
begin
  have h₄ : fact (suitable c₂ c₁ (of f)), { rwa ← suitable_smul_iff i hi },
  have h₅ : fact (suitable c₃ c₂ (of g)), { rwa ← suitable_smul_iff j hj },
  show _ = normed_group_hom.comp_hom _ _,
  resetI,
  simp only [eval_Mbar_pow_smul],
  have H3 := h₃,
  simp only [← gsmul_eq_smul, add_monoid_hom.map_gsmul] at H3 ⊢,
  simp only [gsmul_eq_smul] at H3 ⊢,
  simp only [comp_of, add_monoid_hom.int_smul_apply] at H3 ⊢,
  have h₆ : fact (universal_map.suitable c₃ c₁ (of (f.comp g))),
  { rwa [suitable_smul_iff j hj, suitable_smul_iff i hi] at H3 },
  resetI,
  simp only [← smul_assoc, eval_Mbar_pow_smul],
  rw [smul_assoc, smul_assoc, smul_comm],
  congr' 2,
  simp only [suitable_of_iff] at h₄ h₅ h₆, resetI,
  apply eval_Mbar_pow_comp_of
end

lemma eval_Mbar_pow_comp (f : universal_map m n) (g : universal_map l m)
  [h₁ : fact (f.suitable c₂ c₁)] [h₂ : fact (g.suitable c₃ c₂)]
  [h₃ : fact ((universal_map.comp f g).suitable c₃ c₁)] :
  (universal_map.comp f g).eval_Mbar_pow V S r' c₁ c₃ =
    f.eval_Mbar_pow V S r' c₁ c₂ ≫ g.eval_Mbar_pow V S r' c₂ c₃ :=
begin
  unfreezingI { revert h₁ h₂ h₃ },
  apply free_abelian_group.induction_on'' f; clear f,
  { introsI, simp only [eval_Mbar_pow_zero, zero_comp, pi.zero_apply,
      add_monoid_hom.coe_zero, add_monoid_hom.map_zero] },
  { apply free_abelian_group.induction_on'' g; clear g,
    { introsI, simp only [eval_Mbar_pow_zero, comp_zero, add_monoid_hom.map_zero] },
    { introsI j hj g i hi f h₁ h₂ h₃, apply eval_Mbar_pow_comp_smul_of; assumption },
    { introsI g k hk f hfg IH1 IH2 i hi f₀ h₁ h₂ h₃,
      simp only [add_monoid_hom.map_add],
      sorry } },
  sorry
end

-- lemma eval_Mbar_pow_comp (f : universal_map m n) (g : universal_map l m)
--   [h₁ : fact (f.suitable c₂ c₁)] [h₂ : fact (g.suitable c₃ c₂)]
--   [h₃ : fact ((universal_map.comp f g).suitable c₃ c₁)] :
--   (universal_map.comp f g).eval_Mbar_pow V S r' c₁ c₃ =
--     f.eval_Mbar_pow V S r' c₁ c₂ ≫ g.eval_Mbar_pow V S r' c₂ c₃ :=
-- begin
--   unfreezingI { revert h₁ h₂ h₃ },
--   apply free_abelian_group.induction_on f; clear f,
--   { introsI, simp only [eval_Mbar_pow_zero, zero_comp, pi.zero_apply,
--       add_monoid_hom.coe_zero, add_monoid_hom.map_zero] },
--   { apply free_abelian_group.induction_on g; clear g,
--     { introsI, simp only [eval_Mbar_pow_zero, comp_zero, add_monoid_hom.map_zero] },
--     { introsI g f h₁ h₂ h₃, apply eval_Mbar_pow_comp_of },
--     { introsI g IH f h₁ h₂ h₃,
--       rw suitable_neg_iff at h₂,
--       have : fact (suitable (of (f.comp g)) c₃ c₁),
--       { rw ← suitable_neg_iff, refine (suitable_congr _ _ _ _ _).mp h₃,
--         simp only [comp_of, add_monoid_hom.map_neg] },
--       resetI,
--       show _ = normed_group_hom.comp_hom _ _,
--       simp only [comp_of, add_monoid_hom.map_neg, eval_Mbar_pow_neg,
--           pi.neg_apply, neg_inj, add_monoid_hom.coe_neg],
--       apply IH },
--     { introsI g₁ g₂ IH1 IH2 f h₁ h₂ h₃, } },
--   -- show _ = normed_group_hom.comp_hom (g.eval_Mbar_pow V S r' c₂ c₃) _,
--   -- simp only [eval_Mbar_pow, add_monoid_hom.map_sum, add_monoid_hom.sum_apply],
--   -- rw finset.sum_sigma',
-- end

lemma eval_Mbar_pow_comp_res (f : universal_map m n)
  [fact (f.suitable c₂ c₁)] [fact (f.suitable c₄ c₃)] [fact (c₃ ≤ c₁)] [fact (c₄ ≤ c₂)] :
  f.eval_Mbar_pow V S r' c₁ c₂ ≫ LCC_Mbar_pow.res V S r' c₄ c₂ m =
  LCC_Mbar_pow.res V S r' c₃ c₁ n ≫ f.eval_Mbar_pow V S r' c₃ c₄ :=
sorry

instance suitable_of_mul_left
  (f : universal_map m n) (c c₁ c₂ : ℝ≥0) [fact (f.suitable c₁ c₂)] :
  fact (f.suitable (c * c₁) (c * c₂)) := sorry

end universal_map

namespace package

def suitable (BD : package) (c : ℕ → ℝ≥0) : Prop := sorry

variables (BD : package) (cs : ℕ → ℝ≥0) (i : ℕ) [fact (BD.suitable cs)]

-- instance nonneg_of_suitable : fact (0 ≤ cs i) := sorry

instance basic_suitable_of_suitable : fact ((BD.map i).suitable (cs i) (cs (i+1))) := sorry

instance suitable_of_suitable :
  fact ((universal_map.comp (BD.map i) (BD.map (i+1))).suitable (cs i) (cs (i+2))) :=
sorry

instance suitable_of_mul_right [fact (c₁ ≤ c₂)] : fact ((c₁ * cs i) ≤ (c₂ * cs i)) := sorry

-- sanity check
lemma exists_suitable : ∃ c, BD.suitable c := sorry

end package

end breen_deligne


/-
TODO: Do we want to define the `T⁻¹`-invariants as a kernel,
or would it be better to use equalizers?
-/
/-- The space `V-hat(Mbar_{r'}(S)_{≤c}^a)^{T⁻¹}`. -/
def LCC_Mbar_pow_Tinv [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)]
  [normed_with_aut r V] :
  NormedGroup :=
kernel ((LCC_Mbar_pow.Tinv V S r' c a) - (normed_with_aut.T.inv ≫ (LCC_Mbar_pow.res V S r' _ _ a)))

namespace LCC_Mbar_pow_Tinv

def res [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  LCC_Mbar_pow_Tinv V S r r' c₂ a ⟶ LCC_Mbar_pow_Tinv V S r r' c₁ a :=
kernel.lift _ (kernel.ι _ ≫ LCC_Mbar_pow.res _ _ _ _ _ _)
begin
  rw category.assoc,
  -- now we need to know that `res` commutes with the two types of `Tinv`
  ext v,
  dsimp,
  simp only [pi.zero_apply, normed_group_hom.coe_sub, coe_comp, pi.sub_apply],
  sorry
end

lemma res_comp_res [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)]
  [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ c₃)]
  [normed_with_aut r V] :
  res V S r r' c₂ c₃ a ≫ res V S r r' c₁ c₂ a = res V S r r' c₁ c₃ a :=
sorry

@[simp] lemma res_refl [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] [fact (c ≤ c)]
  [normed_with_aut r V] :
  res V S r r' c c a = 𝟙 _ :=
sorry

end LCC_Mbar_pow_Tinv

variables [fact (0 < r)] [normed_with_aut r V]
variables [fact (0 < r')] [fact (r' ≤ 1)]

open breen_deligne

variables [normed_with_aut r V]

-- -- move this
-- instance fact_mul_nonneg : fact (0 ≤ c₁ * c₂) := mul_nonneg ‹_› ‹_›

def Mbar_complex (BD : breen_deligne.package) (c' : ℕ → ℝ) [fact (BD.suitable c')] :
  cochain_complex NormedGroup :=
{ X := int.extend_from_nat 0 $ λ i, LCC_Mbar_pow_Tinv V S r r' (c * c' i) (BD.rank i),
  d := int.extend_from_nat 0 $ λ i, (BD.map i).eval_Mbar_Tinv V S r r' (c * c' i) (c * c' (i+1)),
  d_squared' :=
  begin
    ext1 ⟨i⟩,
    { dsimp,
      simp only [pi.comp_apply, pi.zero_apply],
      erw ← universal_map.eval_Mbar_Tinv_comp V S r r' _ (c * c' (i+1)) _ (BD.map i) (BD.map (i+1)),
      rw [BD.map_comp_map, universal_map.eval_Mbar_Tinv_zero],
      apply_instance },
    { show 0 ≫ _ = 0, rw [zero_comp] }
  end }

@[simp] lemma Mbar_complex.d_neg_succ_of_nat
  (BD : breen_deligne.package) (c' : ℕ → ℝ) [fact (BD.suitable c')] (n : ℕ) :
  (Mbar_complex V S r r' c BD c').d -[1+n] = 0 := rfl

-- move this
instance nnreal.fact_nonneg_unop_op (c : ℝ≥0ᵒᵖ) :
  fact ((0 : ℝ) ≤ (unop c : ℝ≥0)) := nnreal.coe_nonneg _

def Mbar_system (BD : breen_deligne.package) (c' : ℕ → ℝ) [fact (BD.suitable c')] :
  system_of_complexes :=
{ obj := λ c, Mbar_complex V S r r' (unop c : ℝ≥0) BD c',
  map := λ c₂ c₁ h,
  { f := int.extend_from_nat 0 $ λ i,
    by { haveI : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₂ : ℝ≥0)) := h.unop.down.down,
      exact LCC_Mbar_pow_Tinv.res V S r r' _ _ (BD.rank i) },
    comm' :=
    begin
      ext1 ⟨i⟩,
      { dsimp [int.extend_from_nat],
        apply universal_map.eval_Mbar_Tinv_comp_res },
      { dsimp [int.extend_from_nat],
        simp only [Mbar_complex.d_neg_succ_of_nat, zero_comp] }
    end },
  map_id' :=
  begin
    intro c,
    ext ⟨i⟩ : 2,
    { dsimp [int.extend_from_nat],
      rw LCC_Mbar_pow_Tinv.res_refl V S r r' _ _, refl },
    { dsimp [int.extend_from_nat], ext }
  end,
  map_comp' :=
  begin
    intros c₃ c₂ c₁ h h',
    haveI H' : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₂ : ℝ≥0)) := h'.unop.down.down,
    haveI H : fact (((unop c₂ : ℝ≥0) : ℝ) ≤ (unop c₃ : ℝ≥0)) := h.unop.down.down,
    have : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₃ : ℝ≥0)) := le_trans H' H,
    ext ⟨i⟩ : 2,
    { dsimp [int.extend_from_nat],
      rw LCC_Mbar_pow_Tinv.res_comp_res V S r r' _ _ _ _ },
    { dsimp [int.extend_from_nat],
      rw zero_comp },
  end }
