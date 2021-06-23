import data.int.basic

namespace int

lemma nat_abs_sub_le (a b : ℤ) : nat_abs (a - b) ≤ nat_abs a + nat_abs b :=
by { rw [sub_eq_add_neg, ← int.nat_abs_neg b], apply nat_abs_add_le }

end int
