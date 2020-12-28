import system_of_complexes
import breen_deligne
import locally_constant.Vhat
import Mbar.basic

import for_mathlib.CompHaus

noncomputable theory

open opposite
open_locale nnreal
local attribute [instance] type_pow

def int.extend_from_nat {X : ℤ → Sort*} (x : Π i, X i) (f : Π i : ℕ, X i) : Π i, X i
| (n : ℕ)   := f n
| i@-[1+n]  := x i

variables (V : NormedGroup) (S : Type*) (r r' c c' c₁ c₂ c₃ : ℝ) [fintype S]

/-- The functor `V-hat`, from compact Hausdorff spaces to normed groups. -/
def hat := NormedGroup.LCC.obj V

/-- The space `V-hat(Mbar_{r'}(S)_{≤c}^a)`. -/
def LCC_Mbar_pow (r' : ℝ) (c : ℝ) (a : ℕ) [fact (0 < r')] : NormedGroup :=
(hat V).obj (op $ CompHaus.of ((Mbar r' S c)^a))

/-- The space `V-hat(Mbar_{r'}(S)_{≤c}^a)^{T⁻¹}`. -/
def LCC_Mbar_pow_Tinv (V : NormedGroup) (S : Type*) (r' : ℝ) (c : ℝ) (a : ℕ) [fact (0 < r')] :
  NormedGroup :=
sorry

def LCC_Mbar_pow_Tinv.res (a : ℕ) [fact (0 < r')] [fact (c₁ ≤ c₂)] :
  LCC_Mbar_pow_Tinv V S r' c₂ a ⟶ LCC_Mbar_pow_Tinv V S r' c₁ a :=
sorry

namespace breen_deligne
variables [fact (0 < r')] {l m n : ℕ}

namespace basic_universal_map

/-- Addition puts goes from `Mbar r' S c` to `Mbar r' S c'` for suitable `c'`.
This predicate says what *suitable* means for basic universal maps.
See Lemma 9.11 of [Analytic]. -/
def suitable (f : basic_universal_map m n) (c c' : ℝ) : Prop := sorry

def eval_Mbar (f : basic_universal_map m n) [fact (f.suitable c c')] :
  (LCC_Mbar_pow_Tinv V S r' c n) ⟶ (LCC_Mbar_pow_Tinv V S r' c' m) :=
sorry

lemma eval_Mbar_zero [fact ((0 : basic_universal_map m n).suitable c c')] :
  (0 : basic_universal_map m n).eval_Mbar V S r' c c' = 0 :=
sorry

lemma eval_Mbar_comp (f : basic_universal_map m n) (g : basic_universal_map l m)
  [fact (f.suitable c₁ c₂)] [fact (g.suitable c₂ c₃)] [fact ((f.comp g).suitable c₁ c₃)] :
  (f.comp g).eval_Mbar V S r' c₁ c₃ = f.eval_Mbar V S r' c₁ c₂ ≫ g.eval_Mbar V S r' c₂ c₃ :=
sorry

end basic_universal_map

namespace universal_map

/-- Addition puts goes from `Mbar r' S c` to `Mbar r' S c'` for suitable `c'`.
This predicate says what *suitable* means for universal maps.
See Lemma 9.11 of [Analytic]. -/
def suitable (f : universal_map m n) (c c' : ℝ) : Prop := sorry

def eval_Mbar {m n : ℕ} (f : universal_map m n) [fact (f.suitable c c')] :
  (LCC_Mbar_pow_Tinv V S r' c n) ⟶ (LCC_Mbar_pow_Tinv V S r' c' m) :=
sorry

lemma eval_Mbar_zero [fact ((0 : universal_map m n).suitable c c')] :
  (0 : universal_map m n).eval_Mbar V S r' c c' = 0 :=
sorry

lemma eval_Mbar_comp (f : universal_map m n) (g : universal_map l m)
  [fact (f.suitable c₁ c₂)] [fact (g.suitable c₂ c₃)]
  [fact ((universal_map.comp f g).suitable c₁ c₃)] :
  (universal_map.comp f g).eval_Mbar V S r' c₁ c₃ =
    f.eval_Mbar V S r' c₁ c₂ ≫ g.eval_Mbar V S r' c₂ c₃ :=
sorry

instance suitable_of_mul_left
  (f : universal_map m n) (c c₁ c₂ : ℝ) [fact (f.suitable c₁ c₂)] :
  fact (f.suitable (c * c₁) (c * c₂)) := sorry

end universal_map

def package.suitable (BD : package) (c : ℕ → ℝ) : Prop := sorry

instance suitable_of_suitable (BD : package) (c : ℕ → ℝ) (i : ℕ) [fact (BD.suitable c)] :
  fact ((BD.map i).suitable (c i) (c (i+1))) :=
sorry

instance suitable_of_suitable₂ (BD : package) (c : ℕ → ℝ) (i : ℕ) [fact (BD.suitable c)] :
  fact ((universal_map.comp (BD.map i) (BD.map (i+1))).suitable (c i) (c (i+2))) :=
sorry

instance suitable_of_mul_right (BD : package) (c : ℕ → ℝ) (i : ℕ) [fact (BD.suitable c)]
  [fact (c₁ ≤ c₂)] :
  fact ((c₁ * c i) ≤ (c₂ * c i)) := sorry

end breen_deligne

open breen_deligne

def Mbar_complex [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' < 1)]
  (BD : breen_deligne.package) (c' : ℕ → ℝ) [fact (BD.suitable c')]
  (V : NormedGroup) [normed_with_aut r V]
  (S : Type*) [fintype S] : cochain_complex NormedGroup :=
{ X := int.extend_from_nat 0 $ λ i, LCC_Mbar_pow_Tinv V S r' (c * c' i) (BD.rank i),
  d := int.extend_from_nat 0 $ λ i,
  show LCC_Mbar_pow_Tinv V S r' (c * c' i) (BD.rank i) ⟶
       LCC_Mbar_pow_Tinv V S r' (c * c' (i+1)) (BD.rank (i+1)),
  from (BD.map i).eval_Mbar _ _ _ _ _, -- V S r' (c * c' i) (c * c' (i+1)),
  d_squared' :=
  begin
    ext1 i,
    cases i,
    { show (BD.map i).eval_Mbar V S r' (c * c' i) (c * c' (i + 1)) ≫
           (BD.map (i+1)).eval_Mbar V S r' (c * c' (i+1)) (c * c' (i + 2)) = _,
      erw ← universal_map.eval_Mbar_comp V S r' _ (c * c' (i+1)) _ (BD.map i) (BD.map (i+1)),
      { rw [BD.map_comp_map, universal_map.eval_Mbar_zero], refl },
      apply_instance },
    { dsimp [int.extend_from_nat], simp only [pi.zero_apply, category_theory.limits.zero_comp] }
  end }

variables [normed_with_aut r V]

def Mbar_system [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' < 1)]
  (BD : breen_deligne.package) (c' : ℕ → ℝ) [fact (BD.suitable c')] :
  system_of_complexes :=
{ obj := λ c, Mbar_complex r r' (unop c : ℝ≥0) BD c' V S,
  map := λ c₂ c₁ h,
  { f := int.extend_from_nat 0 $ λ i,
    show LCC_Mbar_pow_Tinv V S r' ((unop c₂ : ℝ≥0) * c' i) (BD.rank i) ⟶
         LCC_Mbar_pow_Tinv V S r' ((unop c₁ : ℝ≥0) * c' i) (BD.rank i),
    by { haveI : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₂ : ℝ≥0)) := h.unop.down.down,
      exact LCC_Mbar_pow_Tinv.res V S r' _ _ (BD.rank i) },
    comm' := sorry },
  map_id' := sorry,
  map_comp' := sorry }
