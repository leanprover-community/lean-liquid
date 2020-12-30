import system_of_complexes
import breen_deligne
import locally_constant.Vhat
import Mbar.basic

import for_mathlib.CompHaus

noncomputable theory

open opposite category_theory category_theory.limits
open_locale nnreal
local attribute [instance] type_pow

def int.extend_from_nat {X : ℤ → Sort*} (x : Π i, X i) (f : Π i : ℕ, X i) : Π i, X i
| (n : ℕ)   := f n
| i@-[1+n]  := x i

variables (V : NormedGroup) (S : Type*) (r r' c c' c₁ c₂ c₃ : ℝ) (a : ℕ) [fintype S]

/-- The functor `V-hat`, from compact Hausdorff spaces to normed groups. -/
abbreviation hat := NormedGroup.LCC.obj V

/-- The space `V-hat(Mbar_{r'}(S)_{≤c}^a)`. -/
def LCC_Mbar_pow [fact (0 < r')] : NormedGroup :=
(hat V).obj (op $ CompHaus.of ((Mbar r' S c)^a))

-- Achtung! Achtung! It is very important that the `[normed_with_aut r V]` instance comes last!
-- Reason: `r` is an out_param, so it should be fixed as soon as possible
-- by searching for `[normed_aut ?x_0 V]`
-- and Lean tries to fill in the typeclass assumptions from right to left.
-- Otherwise it might go on a wild goose chase for `[fact (0 < r)]`...
instance LCC_Mbar_pow.normed_with_aut [fact (0 < r)] [fact (0 < r')] [normed_with_aut r V] :
  normed_with_aut r (LCC_Mbar_pow V S r' c a) :=
NormedGroup.normed_with_aut_LCC V _ r

def LCC_Mbar_pow.res [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  LCC_Mbar_pow V S r' c₂ a ⟶ LCC_Mbar_pow V S r' c₁ a :=
(hat V).map $ has_hom.hom.op
⟨λ x, Mbar.cast_le ∘ x,
  continuous_pi $ λ i, (Mbar.continuous_cast_le r' S c₁ c₂).comp (continuous_apply i)⟩

def LCC_Mbar_pow.Tinv [fact (0 < r')] :
  LCC_Mbar_pow V S r' (c / r') a ⟶ LCC_Mbar_pow V S r' c a :=
(hat V).map $ has_hom.hom.op
⟨λ x, Mbar.Tinv ∘ x,
  continuous_pi $ λ i, (Mbar.continuous_Tinv r' S c).comp (continuous_apply i)⟩

-- move this
instance fix_my_name [h1 : fact (0 < r')] [h2 : fact (r' ≤ 1)] [h3 : fact (0 ≤ c)] : fact (c ≤ c / r') :=
begin
  rw le_div_iff h1,
  nth_rewrite 1 ← mul_one c,
  exact mul_le_mul (le_of_eq rfl) h2 (le_of_lt h1) h3,
end

-- move this
instance fix_my_name₂ [h1 : fact (0 < r')] [h2 : fact (0 ≤ c)] : fact (0 ≤ c / r') := by simpa [le_div_iff h1]

-- move this
instance fix_my_name₃ [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  fact (c₁ / r' ≤ c₂ / r') :=
by { rwa [div_eq_inv_mul, div_eq_inv_mul, mul_le_mul_left], rwa [inv_pos] }

/-- The space `V-hat(Mbar_{r'}(S)_{≤c}^a)^{T⁻¹}`. -/
def LCC_Mbar_pow_Tinv [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] [fact (0 ≤ c)]
  [normed_with_aut r V] :
  NormedGroup :=
kernel ((LCC_Mbar_pow.Tinv V S r' c a) - (normed_with_aut.T.hom ≫ (LCC_Mbar_pow.res V S r' _ _ a)))

def LCC_Mbar_pow_Tinv.res [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)]
  [fact (0 ≤ c₁)] [fact (0 ≤ c₂)] [fact (c₁ ≤ c₂)] [normed_with_aut r V] :
  LCC_Mbar_pow_Tinv V S r r' c₂ a ⟶ LCC_Mbar_pow_Tinv V S r r' c₁ a :=
kernel.lift _ (kernel.ι _ ≫ LCC_Mbar_pow.res _ _ _ _ _ _)
begin
  rw category.assoc,
  -- now we need to know that `res` commutes with the two types of `Tinv`
  sorry
end

variables [fact (0 < r)] [normed_with_aut r V]
variables [fact (0 < r')] [fact (r' ≤ 1)]
variables [fact (0 ≤ c)] [fact (0 ≤ c')] [fact (0 ≤ c₁)] [fact (0 ≤ c₂)] [fact (0 ≤ c₃)]

namespace breen_deligne

variables {l m n : ℕ}

namespace basic_universal_map

/-- Addition goes from `Mbar r' S c` to `Mbar r' S c'` for suitable `c'`.
This predicate says what *suitable* means for basic universal maps.
See Lemma 9.11 of [Analytic]. -/
def suitable (f : basic_universal_map m n) (c c' : ℝ) : Prop := sorry

def eval_Mbar (f : basic_universal_map m n) [fact (f.suitable c c')] :
  (LCC_Mbar_pow_Tinv V S r r' c n) ⟶ (LCC_Mbar_pow_Tinv V S r r' c' m) :=
sorry

lemma eval_Mbar_zero [fact ((0 : basic_universal_map m n).suitable c c')] :
  (0 : basic_universal_map m n).eval_Mbar V S r r' c c' = 0 :=
sorry

lemma eval_Mbar_comp (f : basic_universal_map m n) (g : basic_universal_map l m)
  [fact (f.suitable c₁ c₂)] [fact (g.suitable c₂ c₃)] [fact ((f.comp g).suitable c₁ c₃)] :
  (f.comp g).eval_Mbar V S r r' c₁ c₃ = f.eval_Mbar V S r r' c₁ c₂ ≫ g.eval_Mbar V S r r' c₂ c₃ :=
sorry

end basic_universal_map

namespace universal_map

/-- Addition goes from `Mbar r' S c` to `Mbar r' S c'` for suitable `c'`.
This predicate says what *suitable* means for universal maps.
See Lemma 9.11 of [Analytic]. -/
def suitable (f : universal_map m n) (c c' : ℝ) : Prop := sorry

def eval_Mbar {m n : ℕ} (f : universal_map m n) [fact (f.suitable c c')] :
  (LCC_Mbar_pow_Tinv V S r r' c n) ⟶ (LCC_Mbar_pow_Tinv V S r r' c' m) :=
sorry

lemma eval_Mbar_zero [fact ((0 : universal_map m n).suitable c c')] :
  (0 : universal_map m n).eval_Mbar V S r r' c c' = 0 :=
sorry

lemma eval_Mbar_comp (f : universal_map m n) (g : universal_map l m)
  [fact (f.suitable c₁ c₂)] [fact (g.suitable c₂ c₃)]
  [fact ((universal_map.comp f g).suitable c₁ c₃)] :
  (universal_map.comp f g).eval_Mbar V S r r' c₁ c₃ =
    f.eval_Mbar V S r r' c₁ c₂ ≫ g.eval_Mbar V S r r' c₂ c₃ :=
sorry

instance suitable_of_mul_left
  (f : universal_map m n) (c c₁ c₂ : ℝ) [fact (f.suitable c₁ c₂)] :
  fact (f.suitable (c * c₁) (c * c₂)) := sorry

end universal_map


namespace package

def suitable (BD : package) (c : ℕ → ℝ) : Prop := sorry

variables (BD : package) (cs : ℕ → ℝ) (i : ℕ) [fact (BD.suitable cs)]

instance nonneg_of_suitable : fact (0 ≤ cs i) := sorry

instance basic_suitable_of_suitable : fact ((BD.map i).suitable (cs i) (cs (i+1))) := sorry

instance suitable_of_suitable :
  fact ((universal_map.comp (BD.map i) (BD.map (i+1))).suitable (cs i) (cs (i+2))) :=
sorry

instance suitable_of_mul_right [fact (c₁ ≤ c₂)] : fact ((c₁ * cs i) ≤ (c₂ * cs i)) := sorry

-- sanity check
lemma exists_suitable : ∃ c, BD.suitable c := sorry

end package

end breen_deligne

open breen_deligne

variables [normed_with_aut r V]

-- move this
instance fact_mul_nonneg : fact (0 ≤ c₁ * c₂) := mul_nonneg ‹_› ‹_›

def Mbar_complex (BD : breen_deligne.package) (c' : ℕ → ℝ) [fact (BD.suitable c')] :
  cochain_complex NormedGroup :=
{ X := int.extend_from_nat 0 $ λ i, LCC_Mbar_pow_Tinv V S r r' (c * c' i) (BD.rank i),
  d := int.extend_from_nat 0 $ λ i,
  show LCC_Mbar_pow_Tinv V S r r' (c * c' i) (BD.rank i) ⟶
       LCC_Mbar_pow_Tinv V S r r' (c * c' (i+1)) (BD.rank (i+1)),
  from (BD.map i).eval_Mbar V S r r' (c * c' i) (c * c' (i+1)),
  d_squared' :=
  begin
    ext1 ⟨i⟩,
    { dsimp,
      have aux := BD.map_comp_map i,
      sorry },
    -- the proof below used to work... now they time out :sad:
    -- { show (BD.map i).eval_Mbar V S r r' (c * c' i) (c * c' (i + 1)) ≫
    --        (BD.map (i+1)).eval_Mbar V S r r' (c * c' (i+1)) (c * c' (i + 2)) = _,
    --   erw ← universal_map.eval_Mbar_comp V S r r' _ (c * c' (i+1)) _ (BD.map i) (BD.map (i+1)),
    --   { rw [BD.map_comp_map, universal_map.eval_Mbar_zero], refl },
    --   apply_instance },
    { show 0 ≫ _ = 0, rw [zero_comp] }
  end }

instance nnreal.fact_nonneg_unop_op (c : ℝ≥0ᵒᵖ) :
  fact ((0 : ℝ) ≤ (unop c : ℝ≥0)) := nnreal.coe_nonneg _

def Mbar_system (BD : breen_deligne.package) (c' : ℕ → ℝ) [fact (BD.suitable c')] :
  system_of_complexes :=
{ obj := λ c, Mbar_complex V S r r' (unop c : ℝ≥0) BD c',
  map := λ c₂ c₁ h,
  { f := int.extend_from_nat 0 $ λ i,
    show LCC_Mbar_pow_Tinv V S r r' ((unop c₂ : ℝ≥0) * c' i) (BD.rank i) ⟶
         LCC_Mbar_pow_Tinv V S r r' ((unop c₁ : ℝ≥0) * c' i) (BD.rank i),
    by { haveI : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₂ : ℝ≥0)) := h.unop.down.down,
      exact LCC_Mbar_pow_Tinv.res V S r r' _ _ (BD.rank i) },
    comm' := sorry },
  map_id' := sorry,
  map_comp' := sorry }
