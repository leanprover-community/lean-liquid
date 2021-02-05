import for_mathlib.normed_group_hom
import Mbar.Mbar_le
import pseudo_normed_group.breen_deligne
import breen_deligne.suitable

/-!
# The interplay between Breen--Deligne data and `Mbar_le`

In this file we define how `universal_map`s
(typically part of some BD package)
act on powers of the spaces `Mbar_le r' S c`.
This is not completely straight-forward, since `Mbar_le r' S c`
is not stable under addition: the `c` changes.
We therefore have some sort of "moving target".

We also show that the resulting maps are continuous
for the profinite topology on `Mbar_le`.
-/

local attribute [instance] type_pow

noncomputable theory

open_locale big_operators nnreal

open normed_group_hom normed_group

namespace breen_deligne

namespace basic_universal_map

variables {k l m n : ℕ}
variables (r' : ℝ≥0) (S : Type*) (c c₁ c₂ c₃ : ℝ≥0) [fintype S]
variables (f : basic_universal_map m n)

/-- `f.eval_Mbar_le` for `f : basic_universal_map m n` is
the map `(Mbar_le r' S c₁)^m → (Mbar_le r' S c₂)^n` induced
by the natural map `(Mbar r' S)^m → (Mbar r' S)^n` associated with `f`. -/
def eval_Mbar_le [H : f.suitable c₁ c₂] :
  ((Mbar_le r' S c₁)^m) → ((Mbar_le r' S c₂)^n) :=
Mbar_le.hom_of_normed_group_hom' r' S c₁ c₂ (f.sup_mul_le c₁ c₂) (f.eval_png (Mbar r' S)) $
λ c F hF, eval_png_mem_filtration _ _ hF

@[simp] lemma eval_Mbar_le_apply [f.suitable c₁ c₂]
  (x : (Mbar_le r' S c₁)^m) (j : fin n) (s : S) (i : ℕ) :
  (f.eval_Mbar_le r' S c₁ c₂ x j) s i = f.eval_png (Mbar r' S) (λ i, x i) j s i :=
rfl

@[simp] lemma eval_Mbar_le_zero : eval_Mbar_le r' S c₁ c₂ (0 : basic_universal_map m n) = 0 :=
begin
  ext j s i,
  simp only [eval_Mbar_le, pi.zero_apply, Mbar_le.coe_hom_of_normed_group_hom'_apply,
    Mbar.coe_zero, eval_png_zero, add_monoid_hom.coe_zero],
  refl
end

lemma eval_Mbar_le_comp (f : basic_universal_map m n) (g : basic_universal_map l m)
  [f.suitable c₂ c₁] [g.suitable c₃ c₂] [(f.comp g).suitable c₃ c₁] :
  (f.comp g).eval_Mbar_le r' S c₃ c₁ = f.eval_Mbar_le r' S c₂ c₁ ∘ g.eval_Mbar_le r' S c₃ c₂ :=
begin
  ext j s i,
  simp only [eval_Mbar_le, Mbar_le.coe_hom_of_normed_group_hom'_apply],
  rw eval_png_comp,
  simp only [add_monoid_hom.coe_comp, function.comp_app],
  congr' 2,
  ext,
  simp only [Mbar_le.coe_hom_of_normed_group_hom'_apply, Mbar_le.coe_coe_to_fun],
end

open add_monoid_hom (apply)

lemma eval_Mbar_le_continuous [f.suitable c₁ c₂] :
  continuous (f.eval_Mbar_le r' S c₁ c₂) :=
Mbar_le.hom_of_normed_group_hom'_continuous _ _ _ _ (f.sup_mul_le c₁ c₂) _ _ $
begin
  intro M,
  use M,
  intros F hF j s i hi,
  rw eval_png_apply,
  simp only,
  let Φ : Mbar r' S →+ S → ℕ → ℤ := add_monoid_hom.mk' coe_fn (λ _ _, rfl),
  show apply _ i (apply _ s (Φ (∑ (i : fin m), f j i • F i))) = 0,
  simp only [add_monoid_hom.map_sum, ← gsmul_eq_smul, add_monoid_hom.map_gsmul],
  apply fintype.sum_eq_zero,
  intro k,
  simp only [add_monoid_hom.apply_apply, add_monoid_hom.coe_mk'],
  rw [hF _ _ _ hi, gsmul_zero]
end

end basic_universal_map

end breen_deligne

#lint- only unused_arguments def_lemma doc_blame
