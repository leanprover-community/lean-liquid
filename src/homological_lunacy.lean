import algebra.category.Group
import tactic

open category_theory

structure cochain_complex extends ℤ ⥤ AddCommGroup :=
(is_complex : ∀ (i j : ℤ) (h : i + 2 ≤ j), map (hom_of_le (show i ≤ j, by linarith)) = 0)

variables {C : cochain_complex} {i j k : ℤ}

/-- `C.d` is the differential `C i ⟶ C (i+1)` for a cochain complex `C`. -/
def d : C.obj i ⟶ C.obj j :=
if h : i ≤ j then C.map (hom_of_le h) else 0

lemma d_comp_d (h : i + 2 ≤ k) :
  (d : C.obj i ⟶ C.obj j) ≫ (d : C.obj j ⟶ C.obj k) = 0 :=
begin
  delta d,
  by_cases h12 : i ≤ j,
  { by_cases h23 : j ≤ k,
    { rw [dif_pos h12, dif_pos h23, ← functor.map_comp],
      exact C.is_complex i k h },
    { rw dif_neg h23, rw limits.comp_zero } },
  { rw dif_neg h12, rw limits.zero_comp }
end

lemma d_d (h : i + 2 ≤ k) (x : C.obj i) :
  (d (d x : C.obj j) : C.obj k) = 0 :=
show ((d : C.obj i ⟶ C.obj j) ≫ (d : C.obj j ⟶ C.obj k)) x = 0,
by { rw d_comp_d h, refl }

example (h : ∀ i : ℤ, ∀ x : C.obj (i+1), (d x : C.obj (i+1+1)) = 0 → ∃ y : C.obj i, d y = x)
  (i : ℤ) (x : C.obj i) (hx : (d x : C.obj (i+1)) = 0) :
  ∃ y : C.obj (i-1), d y = x :=
begin
  specialize h (i-1),
  rw sub_add_cancel at h,
  apply h,
  exact hx
end

example (h : ∀ i : ℤ, ∀ x : C.obj i, (d x : C.obj (i+1)) = 0 → ∃ y : C.obj (i-1), d y = x)
  (i : ℤ) (x : C.obj (i+1)) (hx : (d x : C.obj (i+1+1)) = 0) :
  ∃ y : C.obj i, d y = x :=
begin
  specialize h (i+1),
  rw add_sub_cancel at h,
  apply h,
  exact hx
end
