import .basic

noncomputable theory

namespace category_theory

namespace arrow

class split {C : Type*} [category C] (f : arrow C) :=
(σ : f.right ⟶ f.left)
(is_splitting' : σ ≫ f.hom = 𝟙 _ . obviously)

restate_axiom split.is_splitting'

attribute [simp] split.is_splitting

end arrow

namespace cech

variables {C : Type*} [category C]

open_locale simplicial

/-!
This is the splitting which allows us to obtain the contracting homotopy.
-/
-- A splitting of the Cech nerve
abbreviation cech_splitting {X B : C} (f : X ⟶ B) (g : B ⟶ X) (splitting : g ≫ f = 𝟙 B)
  [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)]
  (n : ℕ) : (cech_obj f) _[n] ⟶ (cech_obj f) _[n+1] :=
limits.wide_pullback.lift limits.wide_pullback.base
(λ i, if hi : i = 0 then limits.wide_pullback.base ≫ g else limits.wide_pullback.π $ ufin.pred i hi) $
by {intros i, split_ifs, all_goals {simp [splitting]}}

lemma face_zero_π {X B : C} (f : X ⟶ B)
  [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)] (n : ℕ) (i : ufin (n+1)) :
  ((cech_obj f).δ 0 : (cech_obj f) _[n+1] ⟶ (cech_obj f) _[n]) ≫ (limits.wide_pullback.π i) =
  limits.wide_pullback.π (ufin.succ i) :=
by {change limits.wide_pullback.lift _ _ _ ≫ _ = _, simpa}

@[simp]
lemma cech_splitting_face_zero {X B : C} (f : X ⟶ B) (g : B ⟶ X) (splitting : g ≫ f = 𝟙 B)
  [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)] (n : ℕ) :
  cech_splitting f g splitting n ≫ (cech_obj f).δ 0 = 𝟙 _ :=
begin
  ext,
  simp only [category_theory.category.id_comp,
    category_theory.category.assoc,
    category_theory.limits.wide_pullback.lift_π,
    category_theory.cech.face_zero_π],
  split_ifs,
  { exact false.elim (ufin.succ_ne_zero _ h) },
  { erw ufin.succ_pred },
  change (_ ≫ (cech_obj f).map _) ≫ _ = _,
  simp,
end

@[simp]
lemma face_π {X B : C} (f : X ⟶ B)
  [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)]
  (n : ℕ) (i : ufin (n+1)) (j : fin (n+2)) :
  ((cech_obj f).δ j : (cech_obj f) _[n+1] ⟶ _) ≫ (limits.wide_pullback.π i) =
  limits.wide_pullback.π (ufin.map (fin.succ_above j) i) :=
begin
  change limits.wide_pullback.lift _ _ _ ≫ _ = _,
  simpa,
end

lemma fin_helper_1 {n} (a : fin (n+1)) (b : fin (n+2)) (hb : b ≠ 0) : b.succ_above a = 0 ↔ a = 0 :=
begin
  split,
  { intro h,
    have : (0 : fin (n+2)) = b.succ_above 0,
    { rw fin.succ_above_below,
      refl,
      exact bot_lt_iff_ne_bot.mpr hb },
    rw this at h,
    exact (fin.succ_above _).injective h },
  { rintro ⟨rfl⟩,
    rw fin.succ_above_below,
    refl,
    change 0 < b,
    exact bot_lt_iff_ne_bot.mpr hb }
end

lemma fin_helper_2 {n} (a : fin (n+1)) : a.cast_succ = 0 ↔ a = 0 := by tidy

lemma fin_helper_3 {n} (a : fin (n+1)) : a.cast_succ ≠ 0 ↔ a ≠ 0 := by simp [not_iff_not, fin_helper_2]

lemma fin_helper_4 {n} (a b : fin (n+2)) (ha : a ≠ 0) (hb : b ≠ 0) :
  ((fin.cast_succ a).succ_above b).pred (λ c, hb $ by {rwa ← fin_helper_1, rwa fin_helper_3}) =
  (fin.cast_succ (a.pred ha)).succ_above (b.pred hb) :=
begin
  by_cases h : b < a,
  { have : a.cast_succ.succ_above b = b.cast_succ, by rwa fin.succ_above_below,
    conv_lhs {
      congr,
      rw this },
    symmetry,
    rw fin.succ_above_below,
    { cases a, cases b, refl },
    exact fin.pred_lt_pred_iff.mpr h },
  { have : a.cast_succ.succ_above b = b.succ,
    { rw fin.succ_above_above,
      exact not_lt.mp h },
    conv_lhs {
      congr,
      rw this },
    symmetry,
    rw fin.succ_above_above,
    simp only [fin.succ_pred, fin.pred_succ],
    mono,
    rwa [fin.pred_le_pred_iff, ← not_lt] },
end

-- TODO: This proof could be cleaned up a bit...
@[simp]
lemma cech_splitting_face {X B : C} (f : X ⟶ B) (g : B ⟶ X) (splitting : g ≫ f = 𝟙 B)
  [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)] (n : ℕ)
  (j : fin (n+2)) (hj : j ≠ 0) :
  cech_splitting f g splitting (n+1) ≫ (cech_obj f).δ j =
  (cech_obj f).δ (j.pred hj) ≫ cech_splitting f g splitting n :=
begin
  ext k,
  simp,
  split_ifs with h1 h2,
  { rw ← category.assoc,
    congr' 1,
    change _ = limits.wide_pullback.lift _ _ _ ≫ _,
    simp },
  { exfalso,
    apply h2,
    replace h1 := equiv.ulift.symm.injective h1,
    rw fin_helper_1 at h1,
    ext1,
    erw h1,
    refl,
    rwa fin_helper_3 },
  { exfalso,
    apply h1,
    rw h,
    apply_fun equiv.ulift,
    erw fin_helper_1,
    refl,
    rwa fin_helper_3 },
  { change _ = limits.wide_pullback.lift _ _ _ ≫ _,
    simp only [category_theory.limits.wide_pullback.lift_π],
    congr,
    ext1,
    dsimp,
    change _ = (fin.cast_succ (j.pred hj)).succ_above _,
    erw fin_helper_4 },
  { change (_ ≫ (cech_obj f).map _) ≫ _ = ((cech_obj f).map _ ≫ _) ≫ _,
    simp },
end

end cech

end category_theory
