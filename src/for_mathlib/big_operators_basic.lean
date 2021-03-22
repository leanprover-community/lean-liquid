import algebra.big_operators.basic


open_locale big_operators
open finset (range)

lemma finset.eq_sum_range_sub {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  f n = f 0 + ∑ i in range n, (f (i+1) - f i) :=
by { rw finset.sum_range_sub, abel }

lemma finset.eq_sum_range_sub' {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  f n = ∑ i in range (n + 1), if i = 0 then f 0 else f i - f (i - 1) :=
begin
  conv_lhs { rw [finset.eq_sum_range_sub f] },
  simp [finset.sum_range_succ', add_comm]
end
