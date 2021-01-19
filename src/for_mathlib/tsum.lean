import topology.algebra.infinite_sum
import topology.instances.nnreal

open_locale big_operators nnreal

lemma tsum_abs_eq_coe_tsum_nnabs {α : Type*} (f : α → ℝ) :
  (∑' i, abs (f i)) = ∑' i, real.nnabs (f i) :=
by simp only [nnreal.coe_nnabs]

open nnreal finset

lemma has_sum_nat_add_iff'' {f : ℕ → ℝ≥0} (k : ℕ) {a : ℝ≥0} :
  has_sum (λ n, f (n + k)) a ↔ has_sum f (a + ∑ i in range k, f i) :=
begin
  unfold has_sum,
  rw ← tendsto_coe,
  rw ← tendsto_coe,
  simp only [coe_sum],
  convert has_sum_nat_add_iff k,
  refl,
  classical,
  rw nnreal.coe_add,
  simp only [coe_sum],
  apply_instance,
end
.
lemma sum_add_tsum_nat_add' {f : ℕ → ℝ≥0} (k : ℕ) (h : summable f) :
  (∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i) :=
by simpa [add_comm] using
  ((has_sum_nat_add_iff'' k).1 ((nnreal.summable_nat_add_iff k).2 h).has_sum).unique h.has_sum

lemma tsum_eq_zero {ι} (f : ι → ℝ≥0) (h : ∀ b, f b = 0) : (∑' b, f b) = 0 :=
by simp only [h, tsum_zero]
#lint- only unused_arguments
