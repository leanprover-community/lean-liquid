import data.sign

namespace int

@[elab_as_eliminator] protected lemma induction_on_iff {p : ℤ → Prop}
  (i : ℤ) (hz : p 0) (h : ∀ i : ℤ, p i ↔ p (i + 1)) : p i :=
begin
  induction i using int.induction_on with i IH i IH,
  { exact hz },
  { rwa ← h },
  { rwa [h, sub_add_cancel], }
end

@[simp] lemma sign_eq_sign (n : ℤ) : n.sign = _root_.sign n :=
begin
  obtain ((_ | _) | _) := n,
  { exact congr_arg coe sign_zero.symm },
  { exact congr_arg coe (sign_pos $ int.succ_coe_nat_pos _).symm },
  { exact congr_arg coe (_root_.sign_neg $ neg_succ_lt_zero _).symm }
end

end int
