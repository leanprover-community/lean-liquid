import for_mathlib.equalizers
import Mbar.Mbar_pow
import system_of_complexes

/-!
# The system of complexes associated with `V` and `Mbar_le r' S c`

In this file we have two main definitions:

* `LCC_Mbar_pow_Tinv` is the normed abelian group `V-hat(Mbar_{r'}(S)_{≤c}^a)^{T⁻¹}`
* `Mbar_system` packages all those normed abelian groups together
  into a system of complexes.
  Those complexes are constructed using Breen--Deligne data.
-/

open_locale classical nnreal
noncomputable theory

open opposite breen_deligne category_theory category_theory.limits

variables (BD : package) (c' : ℕ → ℝ≥0) [BD.suitable c']
variables (V : NormedGroup) (S : Type*) (r r' c c₁ c₂ c₃ c₄ : ℝ≥0) (a : ℕ) [fintype S]

/-- The space `V-hat(Mbar_{r'}(S)_{≤c}^a)^{T⁻¹}`, defined by taking `T⁻¹`-invariants
for two different actions by `T⁻¹`:

* The first comes from the action of `T⁻¹` on `Mbar_{r'}(S)`.
* The second comes from the action of `T⁻¹` on `V`.

We take the equalizer of those two actions.

See the lines just above Definition 9.3 of [Analytic]. -/
def LCC_Mbar_pow_Tinv [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] [normed_with_aut r V] :
  NormedGroup :=
equalizer (LCC_Mbar_pow.Tinv V S r' c a) (normed_with_aut.T.inv ≫ (LCC_Mbar_pow.res V S r' _ _ a))

variables [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] [normed_with_aut r V]

namespace LCC_Mbar_pow_Tinv

/-- The restriction map. -/
def res [fact (c₁ ≤ c₂)] :
  LCC_Mbar_pow_Tinv V S r r' c₂ a ⟶ LCC_Mbar_pow_Tinv V S r r' c₁ a :=
equalizer.map (LCC_Mbar_pow.res _ _ _ _ _ _) (LCC_Mbar_pow.res _ _ _ _ _ _)
(by rw LCC_Mbar_pow.Tinv_res)
begin
  haveI : fact (c₁ ≤ r'⁻¹ * c₂) :=
    le_trans ‹c₁ ≤ c₂› (show fact (c₂ ≤ r'⁻¹ * c₂), by apply_instance),
  rw [category.assoc, LCC_Mbar_pow.res_comp_res,
      ← LCC_Mbar_pow.T_inv_res_assoc, LCC_Mbar_pow.res_comp_res]
end

lemma res_comp_res [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ c₃)] :
  res V S r r' c₂ c₃ a ≫ res V S r r' c₁ c₂ a = res V S r r' c₁ c₃ a :=
by simp only [res, equalizer.map_comp_map, LCC_Mbar_pow.res_comp_res]

@[simp] lemma res_refl [normed_with_aut r V] : res V S r r' c c a = 𝟙 _ :=
by { simp only [res, equalizer.map_id, LCC_Mbar_pow.res_refl], refl }

end LCC_Mbar_pow_Tinv

namespace breen_deligne

namespace universal_map

variables {l m n : ℕ}

/-- `f.eval_Mbar_pow_Tinv` for `f : universal_map m n` is the
homomorphism `LCC_Mbar_pow_Tinv V S r r' c₂ n ⟶ LCC_Mbar_pow_Tinv V S r r' c₁ m`
induced by `f.eval_Mbar_pow`.

The latter is the sum of maps `g.eval_Mbar_pow`,
where `g` is a `basic_universal_map m n` (aka matrix)
occuring in the formal sum `f`.

TODO(jmc): I do not know a precise reference for this definition in [Analytic]. -/
def eval_Mbar_pow_Tinv (f : universal_map m n) [f.suitable c₁ c₂] :
  LCC_Mbar_pow_Tinv V S r r' c₂ n ⟶ LCC_Mbar_pow_Tinv V S r r' c₁ m :=
equalizer.map
  (f.eval_Mbar_pow V S r' ((r'⁻¹ * c₁)) ((r'⁻¹ * c₂)))
  (f.eval_Mbar_pow V S r' c₁ c₂)
  (by rw eval_Mbar_pow_comp_Tinv)
  (by rw [category.assoc, ← eval_Mbar_pow_comp_res V S r' c₁ c₂ (r'⁻¹ * c₁) (r'⁻¹ * c₂) f,
      eval_Mbar_pow_comp_T_inv_assoc])

@[simp] lemma eval_Mbar_pow_Tinv_zero :
  (0 : universal_map m n).eval_Mbar_pow_Tinv V S r r' c₁ c₂ = 0 :=
begin
  apply equalizer.hom_ext,
  simp only [eval_Mbar_pow_Tinv, eval_Mbar_pow_zero, zero_comp, equalizer.map_ι, comp_zero]
end

lemma eval_Mbar_pow_Tinv_comp (g : universal_map m n) (f : universal_map l m)
  [g.suitable c₂ c₃] [f.suitable c₁ c₂] [(comp g f).suitable c₁ c₃] :
  (comp g f).eval_Mbar_pow_Tinv V S r r' c₁ c₃ =
    g.eval_Mbar_pow_Tinv V S r r' c₂ c₃ ≫ f.eval_Mbar_pow_Tinv V S r r' c₁ c₂ :=
by simp only [eval_Mbar_pow_Tinv, equalizer.map_comp_map, ← eval_Mbar_pow_comp]

lemma eval_Mbar_pow_Tinv_comp_res (f : universal_map m n)
  [f.suitable c₁ c₂] [f.suitable c₃ c₄] [fact (c₁ ≤ c₃)] [fact (c₂ ≤ c₄)] :
  f.eval_Mbar_pow_Tinv V S r r' c₃ c₄ ≫ LCC_Mbar_pow_Tinv.res V S r r' c₁ c₃ m =
  LCC_Mbar_pow_Tinv.res V S r r' c₂ c₄ n ≫ f.eval_Mbar_pow_Tinv V S r r' c₁ c₂ :=
begin
  delta eval_Mbar_pow_Tinv LCC_Mbar_pow_Tinv.res,
  rw [equalizer.map_comp_map, equalizer.map_comp_map],
  congr' 1; apply eval_Mbar_pow_comp_res
end

end universal_map

end breen_deligne

/-!
## The system of complexes associated with `V` and `Mbar S`

We are now ready to define the system of complexes occurring in the statement
of Theorems 9.4 and 9.5 of [Analytic].

We do this in two steps: first we define `Mbar_complex`,
which is the complex for a given `c : ℝ≥0`.
Afterwards, we pack these complexes together in the system `Mbar_system`.
-/

open breen_deligne

/-- The complex
`V-hat(Mbar_{r'}(S)_{≤c})^{T⁻¹} ⟶ V-hat(Mbar_{r'}(S)_{≤c_1c}^2)^{T⁻¹} ⟶ ...`

These complexes are packed together in `Mbar_system` into a system of complexes,
as they occur in Theorems 9.4 and 9.5 of [Analytic]. -/
def Mbar_complex (BD : breen_deligne.package) (c' : ℕ → ℝ≥0) [BD.suitable c'] :
  cochain_complex NormedGroup :=
{ /- the objects -/
  X := int.extend_from_nat 0 $ λ i, LCC_Mbar_pow_Tinv V S r r' (c * c' i) (BD.rank i),
  /- the differentials -/
  d := int.extend_from_nat 0 $ λ i, (BD.map i).eval_Mbar_pow_Tinv V S r r' (c * c' (i+1)) (c * c' i),
  d_squared' := /- d^2 = 0 -/
  begin
    ext1 ⟨i⟩,
    { dsimp,
      simp only [pi.comp_apply, pi.zero_apply],
      erw ← universal_map.eval_Mbar_pow_Tinv_comp V S r r' _ (c * c' (i+1)) _ (BD.map i) (BD.map (i+1)),
      simp only [BD.map_comp_map, universal_map.eval_Mbar_pow_Tinv_zero],
      apply_instance },
    { show 0 ≫ _ = 0, rw [zero_comp] }
  end }

@[simp] lemma Mbar_complex.d_neg_succ_of_nat
  (BD : breen_deligne.package) (c' : ℕ → ℝ≥0) [BD.suitable c'] (n : ℕ) :
  (Mbar_complex V S r r' c BD c').d -[1+n] = 0 := rfl

/-- The system of complexes
`V-hat(Mbar_{r'}(S)_{≤c})^{T⁻¹} ⟶ V-hat(Mbar_{r'}(S)_{≤c_1c}^2)^{T⁻¹} ⟶ ...`
occurring in Theorems 9.4 and 9.5 of [Analytic]. -/
def Mbar_system (BD : breen_deligne.package) (c' : ℕ → ℝ≥0) [BD.suitable c'] :
  system_of_complexes :=
{ /- the objects, aka the constituent complexes -/
  obj := λ c, Mbar_complex V S r r' (unop c : ℝ≥0) BD c',
  /- the restriction maps -/
  map := λ c₂ c₁ h,
  { f := int.extend_from_nat 0 $ λ i,
    by { haveI : fact (((unop c₁ : ℝ≥0) : ℝ) ≤ (unop c₂ : ℝ≥0)) := h.unop.down.down,
      exact LCC_Mbar_pow_Tinv.res V S r r' _ _ (BD.rank i) },
    comm' :=
    begin
      ext1 ⟨i⟩,
      { dsimp [int.extend_from_nat],
        apply universal_map.eval_Mbar_pow_Tinv_comp_res },
      { dsimp [int.extend_from_nat],
        simp only [Mbar_complex.d_neg_succ_of_nat, zero_comp] }
    end },
  map_id' := /- the restriction map for `c ≤ c` is the identity -/
  begin
    intro c,
    ext ⟨i⟩ : 2,
    { dsimp [int.extend_from_nat],
      rw LCC_Mbar_pow_Tinv.res_refl V S r r' _ _, refl },
    { dsimp [int.extend_from_nat], ext }
  end,
  map_comp' := /- composition of transition maps is a transition map -/
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
