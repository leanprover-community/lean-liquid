import normed_free_pfpng.basic
import free_pfpng.basic
import condensed.exact

open_locale nnreal big_operators

variables (p : ℝ≥0) (S : Fintype)
variables [fact (0 < p)] [fact (p ≤ 1)]

def free_pfpng_to_normed_free_pfpng :
  free_pfpng_functor ⟶ normed_free_pfpng_functor p :=
{ app := λ S,
  { to_fun := λ f, f,
    map_zero' := rfl,
    map_add' := λ _ _, rfl,
    strict' := begin
      have h0p : 0 < p := fact.out _,
      have hp1 : p ≤ 1 := fact.out _,
      rintro c f (hf : _ ≤ _),
      refine le_trans (finset.sum_le_sum _) hf,
      rintro s -,
      rcases (eq_or_ne (∥f s∥₊) 0) with (h|h),
      { simp only [h, le_zero_iff, nnreal.rpow_eq_zero_iff, eq_self_iff_true,
          ne.def, nnreal.coe_eq_zero, true_and],
        exact h0p.ne' },
      refine (nnreal.rpow_le_rpow_of_exponent_le _ hp1).trans _,
      swap, { rw [nnreal.coe_one, nnreal.rpow_one] },
      rw [← nnreal.coe_nat_abs] at h ⊢,
      norm_cast at h ⊢,
      exact nat.one_le_of_lt (ne.bot_lt h)
    end,
    continuous' := λ c, continuous_of_discrete_topology },
  naturality' := by { intros S T f, ext φ t, refl } }
