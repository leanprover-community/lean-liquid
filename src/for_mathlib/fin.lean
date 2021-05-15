import data.fin

namespace fin

lemma succ_above_eq_zero_iff {n : ℕ} (a : fin (n + 2)) (b : fin (n + 1)) (ha : a ≠ 0) :
  a.succ_above b = 0 ↔ b = 0 :=
begin
  split,
  { intro h,
    have : (0 : fin (n+2)) = a.succ_above 0,
    { rw fin.succ_above_below,
      { refl },
      { exact bot_lt_iff_ne_bot.mpr ha } },
    rw this at h,
    apply (fin.succ_above _).injective h },
  { rintro rfl,
    rw fin.succ_above_below,
    { refl },
    { exact bot_lt_iff_ne_bot.mpr ha } },
end

@[simp]
lemma cast_succ_eq_zero_iff {n : ℕ} (a : fin (n+1)) : a.cast_succ = 0 ↔ a = 0 := by tidy

lemma cast_succ_ne_zero_iff {n : ℕ} (a : fin (n+1)) : a.cast_succ ≠ 0 ↔ a ≠ 0 := by simp

lemma succ_above_pred {n : ℕ} (a : fin (n+2)) (b : fin (n+1)) (ha : a ≠ 0) (hb : b ≠ 0) :
  (a.pred ha).succ_above (b.pred hb) =
  (a.succ_above b).pred (λ c, hb $ by rwa ← succ_above_eq_zero_iff _ _ ha) :=
begin
  by_cases h : b.cast_succ < a,
  { have hbc : b.cast_succ ≠ 0, by simpa [cast_succ_ne_zero_iff],
    have : (b.pred hb).cast_succ = b.cast_succ.pred hbc, by {cases b, refl},
    rw fin.succ_above_below,
    { rwa [this, fin.pred_inj, fin.succ_above_below] },
    { rwa [this, pred_lt_pred_iff] } },
  { have : (b.pred hb).succ = b.succ.pred (fin.succ_ne_zero _), by tidy,
    rw fin.succ_above_above,
    { rw [this, fin.pred_inj, fin.succ_above_above],
      exact not_lt.mp h },
    { have hbc : b.cast_succ ≠ 0, by simpa [cast_succ_ne_zero_iff],
      have : (b.pred hb).cast_succ = b.cast_succ.pred hbc, by {cases b, refl},
      rw [this, fin.pred_le_pred_iff],
      exact not_lt.mp h } }
end

end fin
