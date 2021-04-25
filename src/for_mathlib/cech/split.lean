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

@[simp]
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

end cech

end category_theory
