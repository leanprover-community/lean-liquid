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

end int
