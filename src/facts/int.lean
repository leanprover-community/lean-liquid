import data.int.basic

lemma fact_le_of_add_one_le (q : ℤ) (m : ℤ) [h : fact (q + 1 ≤ m)] : fact (q ≤ m) :=
⟨(int.le_add_one le_rfl).trans h.out⟩

instance fact_two_pow_pos (N : ℕ) : fact (0 < 2 ^ N) :=
⟨pow_pos zero_lt_two _⟩
