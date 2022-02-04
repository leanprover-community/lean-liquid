import Mbar.functor
import laurent_measures.functor

.

/-!
The short exact sequence
```
0 → ℤ[T⁻¹] → ℳ(S, ℤ((T))_r') → ℳ-bar(S)_r' → 0
```
-/

noncomputable theory

open_locale nnreal

variables (r' : ℝ≥0) [fact (0 < r')] (S : Fintype)

-- move me
lemma int.coe_nat_injective : function.injective (coe : ℕ → ℤ) :=
λ m n h, int.coe_nat_inj h

namespace laurent_measures

@[simps] def to_Mbar (F : laurent_measures r' S) : Mbar r' S :=
{ to_fun := λ s n, if n = 0 then 0 else F s n,
  coeff_zero' := λ s, if_pos rfl,
  summable' := λ s, begin
    have := nnreal.summable_comp_injective (F.nnreal_summable s) int.coe_nat_injective,
    refine nnreal.summable_of_le _ this,
    intros n,
    simp only [function.comp_app, zpow_coe_nat],
    split_ifs,
    { simp only [int.nat_abs_zero, nat.cast_zero, zero_mul, zero_le'], },
    { simp only [nnreal.coe_nat_abs], }
  end }

lemma to_Mbar_surjective : function.surjective (to_Mbar r' S) :=
sorry

lemma nnnorm_to_Mbar (F : laurent_measures r' S) : ∥to_Mbar r' S F∥₊ ≤ ∥F∥₊ :=
sorry

@[simps] def to_Mbar_hom : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r'
  (laurent_measures r' S) (Mbar r' S) :=
{ to_fun := to_Mbar r' S,
  map_zero' := by { ext,
    simp only [to_Mbar_to_fun, zero_apply, if_t_t, Mbar.coe_zero, pi.zero_apply], },
  map_add' := λ F G, by { ext, simp only [to_Mbar_to_fun, add_apply, Mbar.coe_add, pi.add_apply],
    split_ifs, { rw add_zero }, { refl } },
  strict' := λ c F (hF : ∥F∥₊ ≤ c), (nnnorm_to_Mbar r' S F).trans hF,
  continuous' := sorry,
  map_Tinv' := λ F, begin
    simp only [Tinv_apply, Mbar.Tinv_apply],
    ext s (_|n),
    { simp only [to_Mbar_to_fun, eq_self_iff_true, if_true, Mbar.Tinv_zero], },
    { simp only [to_Mbar_to_fun, nat.succ_ne_zero, int.coe_nat_succ, shift_to_fun_to_fun,
        Mbar.Tinv_succ], }
  end }

@[simps]
def to_Mbar_fintype_nattrans : laurent_measures.fintype_functor r' ⟶ Mbar.fintype_functor r' :=
{ app := λ S, to_Mbar_hom r' S,
  naturality' := sorry }

end laurent_measures
