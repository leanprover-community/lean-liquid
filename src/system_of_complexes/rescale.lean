import system_of_complexes.basic
import normed_group.rescale

noncomputable theory

namespace system_of_complexes

open category_theory
open_locale nat nnreal

def rescale (r : ℝ≥0) [fact (0 < r)] : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ functor.map_complex_like $ NormedGroup.rescale r

instance rescale.additive (r : ℝ≥0) [fact (0 < r)] : (rescale r).additive :=
sorry

-- can we golf this? speed it up?
def to_rescale (r : ℝ≥0) [fact (0 < r)] : 𝟭 system_of_complexes ⟶ rescale r :=
{ app := λ C,
  { app := λ c, (functor.map_complex_like_nat_trans _ _ $ NormedGroup.to_rescale r).app (C.obj c),
    naturality' := by { intros c₁ c₂ h, ext i : 2, refl } },
  naturality' := λ C₁ C₂ f, by { ext, refl } }

def scale (i j : ℝ≥0) [fact (0 < i)] [fact (0 < j)] : rescale i ⟶ rescale j :=
(whiskering_right _ _ _).map $ functor.map_complex_like_nat_trans _ _ $
  NormedGroup.scale i j

section exact_and_admissible

variables {k K : ℝ≥0} [fact (1 ≤ k)] {m : ℕ} {c₀ : ℝ≥0}

lemma rescale_is_weak_bounded_exact (r : ℝ≥0) [fact (0 < r)] (C : system_of_complexes)
  (hC : C.is_weak_bounded_exact k K m c₀) :
  ((rescale r).obj C).is_weak_bounded_exact k K m c₀ :=
begin
  intros c hc i hi x ε hε,
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc i hi ((@rescale.of r _).symm x) (ε * r) _,
  swap, { exact mul_pos hε ‹_› },
  refine ⟨_, _, rfl, rfl, (@rescale.of r _) y, _⟩,
  erw [rescale.norm_def, rescale.norm_def],
  rwa [div_le_iff, add_mul, mul_assoc, div_mul_cancel],
  { apply ne_of_gt, assumption },
  { assumption },
end

-- TODO: we need a lemma that says that `rescale C` is admissible if `C` is
lemma rescale_admissible (r : ℝ≥0) [fact (0 < r)] (C : system_of_complexes) (hC : C.admissible) :
  ((rescale r).obj C).admissible :=
sorry

end exact_and_admissible

instance (m : ℕ) : fact (0 < m!) :=
nat.factorial_pos _

def rescale_functor : ℕ → (system_of_complexes ⥤ system_of_complexes)
| 0     := 𝟭 _
| 1     := 𝟭 _
| (m+2) := rescale (m+2)!

instance rescale_functor.additive : Π m, (rescale_functor m).additive
| 0     := functor.id.additive
| 1     := functor.id.additive
| (m+2) := show (rescale (m+2)!).additive, from rescale.additive _

def rescale_nat_trans : Π i j, rescale_functor i ⟶ rescale_functor j
| 0     1     := 𝟙 _
| 1     (j+2) := to_rescale (j+2)!
| (i+2) (j+2) := scale (i+2)! (j+2)!
| _     _     := 0


end system_of_complexes
