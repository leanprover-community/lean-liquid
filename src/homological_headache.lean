import algebra.homology.chain_complex
import algebra.category.Group
import tactic.ring

variables (C : cochain_complex AddCommGroup)

open category_theory

section

open tactic

meta def int_magic : tactic unit :=
do (assumption <|> tactic.interactive.ring1 none <|> tactic.interactive.refl) <|>
   target >>= trace

end

/-- Convenience definition:
The identity morphism of an object in the system of complexes
when it is given by different indices that are not
definitionally equal. -/
def congr_hom {i j : ℤ} (h : i = j) :
  C.X i ⟶ C.X j :=
eq_to_hom $ by { subst h }

/-- `C.d` is the differential `C i ⟶ C (i+1)` for a cochain complex `C`. -/
def d {C : cochain_complex AddCommGroup} {i j : ℤ} [hij : fact (i + 1 = j)] :
  C.X i ⟶ C.X j :=
C.d i ≫ congr_hom C hij

-- local notation `d` := differential _ _ _ (by int_magic)

lemma d_rfl (i : ℤ) : @d C i (i+1) rfl = C.d i :=
by { ext, refl }

lemma d_comp_d {i₁ i₂ i₃ : ℤ} (h : fact (i₁ + 1 = i₂)) (h' : fact (i₂ + 1 = i₃)) :
  (d : C.X i₁ ⟶ C.X i₂) ≫ (d : C.X i₂ ⟶ C.X i₃) = 0 :=
begin
  unfreezingI { cases h, cases h' },
  simp only [d_rfl],
  exact homological_complex.d_squared _ _
end

lemma d_d {i₁ i₂ i₃ : ℤ} (h : fact (i₁ + 1 = i₂)) (h' : fact (i₂ + 1 = i₃)) (x : C.X i₁) :
  (d (d x : C.X i₂) : C.X i₃) = 0 :=
show ((d : C.X i₁ ⟶ C.X i₂) ≫ (d : C.X i₂ ⟶ C.X i₃)) x = 0,
by { rw d_comp_d, refl }

instance fact_rfl (i : ℤ) : fact (i = i) := rfl
instance fact_sub_add_one (i : ℤ) : fact (i - 1 + 1 = i) := by { delta fact, ring }
-- instance fact_add_sub_one (i : ℤ) : fact (i + 1 - 1 = i) := by { delta fact, ring }

example (h : ∀ i : ℤ, ∀ x : C.X (i+1), (d x : C.X (i+1+1)) = 0 → ∃ y : C.X i, d y = x)
  (i : ℤ) (x : C.X i) (hx : (d x : C.X (i+1)) = 0) :
  ∃ y : C.X (i-1), d y = x :=
begin
  specialize h (i-1),
  -- rw sub_add_cancel at h,
  simp at h,
end

example (h : ∀ i : ℤ, ∀ x : C.X i, (d x : C.X (i+1)) = 0 → ∃ y : C.X (i-1), d y = x)
  (i : ℤ) (x : C.X (i+1)) (hx : (d x : C.X (i+1+1)) = 0) :
  ∃ y : C.X i, d y = x :=
begin
  specialize h (i+1),
  -- rw add_sub_cancel at h,
  simp at h,
end
