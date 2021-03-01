import data.real.nnreal
import topology.algebra.infinite_sum

open_locale nnreal

def mask_fun (f : ℕ → ℝ≥0) (mask : ℕ → Prop) [∀ n, decidable (mask n)] : ℕ → ℝ≥0 :=
λ n, if mask n then f n else 0

lemma exists_partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
  ∃ (mask : fin N → ℕ → Prop) [∀ i n, decidable (mask i n)], by exactI
    (∀ n, ∃! i, mask i n) ∧ (∀ i, ∑' n, mask_fun f (mask i) n ≤ (∑' n, f n) / N + 1) :=
sorry
