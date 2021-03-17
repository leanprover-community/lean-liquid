import data.real.basic

lemma real.le_of_forall_le_add {x y : ℝ} : x ≤ y ↔ ∀ ε > 0, x ≤ y + ε :=
⟨λ h ε ε_pos, by linarith, le_of_forall_pos_le_add⟩

lemma real.le_of_forall_lt_add {x y : ℝ} : x ≤ y ↔ ∀ ε > 0, x < y + ε :=
begin
  rw real.le_of_forall_le_add,
  split ; intros H ε ε_pos,
  { linarith [H (ε/2) (half_pos ε_pos)] },
  exact (H ε ε_pos).le
end

lemma real.lt_Inf_add_pos {s : set ℝ} (h : bdd_below s) (h' : s.nonempty) {ε : ℝ} (hε : ε > 0) :
  ∃ a ∈ s, a < Inf s + ε :=
(real.Inf_lt _ h' h).1 (lt_add_of_pos_right _ hε)

lemma real.Inf_le_iff {s : set ℝ} (h : bdd_below s) (h' : s.nonempty) {a : ℝ} :
  Inf s ≤ a ↔ ∀ ε > 0, ∃ x ∈ s, x < a + ε :=
begin
  rw real.le_of_forall_lt_add,
  split ; intros H ε ε_pos,
  { exact exists_lt_of_cInf_lt h' (H ε ε_pos) },
  { rcases H ε ε_pos with ⟨x, x_in, hx⟩,
    exact cInf_lt_of_lt h x_in hx }
end
