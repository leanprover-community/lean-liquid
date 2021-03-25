import data.int.basic

instance fact_le_of_add_one_le (q : ℤ) (m : ℤ) [h : fact (q + 1 ≤ m)] : fact (q ≤ m) :=
⟨(int.le_add_one le_rfl).trans h.out⟩
