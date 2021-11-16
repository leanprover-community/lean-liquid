import system_of_complexes.basic
import rescale.normed_group
/-!

# rescaling norms on a system of complexes

This file defines the `rescale` functor which will take a system of complexes of seminormed groups
and systematically rescale all the norms on all the seminormed groups by a constant factor.

-/
noncomputable theory

universe variables u

open category_theory
open_locale nat nnreal

namespace nnreal

def MulLeft (κ : ℝ≥0) : ℝ≥0 ⥤ ℝ≥0 :=
{ obj := λ c, κ * c,
  map := λ c₁ c₂ h, hom_of_le $ mul_le_mul' le_rfl (le_of_hom h) }

def MulRight (κ : ℝ≥0) : ℝ≥0 ⥤ ℝ≥0 :=
{ obj := λ c, c * κ,
  map := λ c₁ c₂ h, hom_of_le $ mul_le_mul' (le_of_hom h) le_rfl }

end nnreal

namespace system_of_complexes

def rescale (r : ℝ≥0) [fact (0 < r)] : system_of_complexes.{u} ⥤ system_of_complexes.{u} :=
(whiskering_right _ _ _).obj $ (SemiNormedGroup.rescale r).map_homological_complex _

lemma rescale_obj (r c : ℝ≥0) [fact (0 < r)] (C : system_of_complexes) (i : ℕ) :
  ↥(((rescale r).obj C) c i) = _root_.rescale r (C c i) := rfl

lemma rescale_d (r c : ℝ≥0) [fact (0 < r)] (C : system_of_complexes) (i j : ℕ)
  (v : (((rescale r).obj C) c i)) :
  (((rescale r).obj C).d i j) v = @rescale.of r _ ((C.d i j) (((@rescale.of r _).symm) v)) :=
rfl

instance rescale.additive (r : ℝ≥0) [fact (0 < r)] : (rescale r).additive :=
{ map_add' := λ X Y f g, by { ext, refl } } -- a heavy refl
.

-- can we golf this? speed it up?
def to_rescale (r : ℝ≥0) [fact (0 < r)] : 𝟭 system_of_complexes ⟶ rescale r :=
{ app := λ C,
  { app := λ c,
    { f := λ _, (SemiNormedGroup.to_rescale r).app _,
      comm' := by { intros, exact ((SemiNormedGroup.to_rescale r).naturality _).symm } },
    naturality' := by { intros c₁ c₂ h, ext i : 2, refl } },
  naturality' := λ C₁ C₂ f, by { ext, refl } }
.

def scale (i j : ℝ≥0) [fact (0 < i)] [fact (0 < j)] : rescale i ⟶ rescale j :=
(whiskering_right _ _ _).map $ nat_trans.map_homological_complex (SemiNormedGroup.scale i j) _

section exact_and_admissible

variables {k K : ℝ≥0} [fact (1 ≤ k)] {m : ℕ} {c₀ : ℝ≥0}

lemma rescale_is_weak_bounded_exact (r : ℝ≥0) [hr : fact (0 < r)] (C : system_of_complexes)
  (hC : C.is_weak_bounded_exact k K m c₀) :
  ((rescale r).obj C).is_weak_bounded_exact k K m c₀ :=
begin
  intros c hc i hi x ε hε,
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc i hi ((@rescale.of r _).symm x) (ε * r) _,
  swap, { exact mul_pos hε hr.out },
  refine ⟨_, _, rfl, rfl, (@rescale.of r _) y, _⟩,
  erw [rescale.norm_def, rescale.norm_def],
  rwa [div_le_iff, add_mul, mul_assoc, div_mul_cancel],
  { apply ne_of_gt, exact hr.out },
  { exact hr.out },
end
.
/-- `rescale C` is admissible if `C` is. -/
lemma rescale_admissible (r : ℝ≥0) [fact (0 < r)] (C : system_of_complexes) (hC : C.admissible) :
  ((rescale r).obj C).admissible :=
{ d_norm_noninc' := begin
    rintro c i j h,
    rintro (v : _root_.rescale r (C c i)), -- rw rescale_obj gives motive issues
    rw [rescale_d, rescale.norm_def, rescale.norm_def, equiv.symm_apply_apply],
    refine div_le_div_of_le_of_nonneg _ _,
    { apply hC.d_norm_noninc' c i j h},
    { exact nnreal.coe_nonneg r },
  end,
  res_norm_noninc := λ c' c i h v, div_le_div_of_le_of_nonneg
    (hC.res_norm_noninc c' c i h _) (nnreal.coe_nonneg r) }

end exact_and_admissible

instance (m : ℕ) : fact (0 < m!) :=
⟨nat.factorial_pos _⟩

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

section scale_index

@[simps]
def ScaleIndexLeft (κ : ℝ≥0) : system_of_complexes ⥤ system_of_complexes :=
(whiskering_left _ _ _).obj (nnreal.MulLeft κ).op

@[simp] lemma ScaleIndexLeft_apply (C : system_of_complexes) (κ c : ℝ≥0) (i : ℕ) :
  (ScaleIndexLeft κ).obj C c i = C (κ * c) i := rfl

def scale_index_left (C : system_of_complexes) (κ : ℝ≥0) := (ScaleIndexLeft κ).obj C

lemma admissible.scale_index_left {C : system_of_complexes} (hC : C.admissible) (κ : ℝ≥0) :
  (C.scale_index_left κ).admissible :=
{ d_norm_noninc' := λ c i j hij, (by { apply admissible.d_norm_noninc C hC (κ * c) i j, }),
  res_norm_noninc := λ c₁ c₂ i hc, hC.res_norm_noninc _ _ i
    (by { resetI, dsimp, apply_instance }) }

lemma is_weak_bounded_exact.scale_index_left
  {C : system_of_complexes} {k K :ℝ≥0} {m : ℕ} (c₀ c₁: ℝ≥0) [fact (1 ≤ k)]
  (hC : C.is_weak_bounded_exact k K m c₀) (κ : ℝ≥0) [hκ : fact (c₀ ≤ κ * c₁)]
  (C_adm : C.admissible) :
  (C.scale_index_left κ).is_weak_bounded_exact k K m c₁ :=
begin
  intros c hc i hi x ε hε,
  dsimp [scale_index_left, ScaleIndexLeft_apply] at x,
  haveI aux1 : fact (k * (κ * c) ≤ κ * (k * c)) := ⟨(mul_left_comm _ _ _).le⟩,
  obtain ⟨i₀, j, hi₀, hj, y, hy⟩ := hC (κ * c) _ i hi (res x) ε hε,
  swap, { exact ⟨hκ.1.trans $ fact.out _⟩, },
  refine ⟨i₀, j, hi₀, hj, y, _⟩,
  simp only [res_res, d_res] at hy,
  refine hy.trans (add_le_add (mul_le_mul le_rfl _ (norm_nonneg _) K.coe_nonneg) le_rfl),
  apply C_adm.res_norm_noninc,
end

@[simps]
def ScaleIndexRight (κ : ℝ≥0) : system_of_complexes ⥤ system_of_complexes :=
(whiskering_left _ _ _).obj (nnreal.MulRight κ).op

@[simp] lemma ScaleIndexRight_apply (C : system_of_complexes) (κ c : ℝ≥0) (i : ℕ) :
  (ScaleIndexRight κ).obj C c i = C (c * κ) i := rfl

def scale_index_right (C : system_of_complexes) (κ : ℝ≥0) := (ScaleIndexRight κ).obj C

lemma admissible.scale_index_right {C : system_of_complexes} (hC : C.admissible) (κ : ℝ≥0) :
  (C.scale_index_right κ).admissible :=
{ d_norm_noninc' := λ c i j hij, (by { apply admissible.d_norm_noninc C hC (c * κ) i j, }),
  res_norm_noninc := λ c₁ c₂ i hc, hC.res_norm_noninc _ _ i
    (by { resetI, dsimp, apply_instance }) }

lemma is_weak_bounded_exact.scale_index_right
  {C : system_of_complexes} {k K :ℝ≥0} {m : ℕ} (c₀ c₁ : ℝ≥0) [fact (1 ≤ k)]
  (hC : C.is_weak_bounded_exact k K m c₀) (κ : ℝ≥0) [hκ : fact (c₀ ≤ κ * c₁)]
  (C_adm : C.admissible) :
  (C.scale_index_right κ).is_weak_bounded_exact k K m c₁ :=
begin
  intros c hc i hi x ε hε,
  dsimp [scale_index_right, ScaleIndexRight_apply] at x,
  haveI aux1 : fact (k * (c * κ) ≤ k * c * κ) := ⟨(mul_assoc _ _ _).ge⟩,
  obtain ⟨i₀, j, hi₀, hj, y, hy⟩ := hC (c * κ) _ i hi (res x) ε hε,
  swap, { rw mul_comm, exact ⟨hκ.1.trans $ fact.out _⟩, },
  refine ⟨i₀, j, hi₀, hj, y, _⟩,
  simp only [res_res, d_res] at hy,
  refine hy.trans (add_le_add (mul_le_mul le_rfl _ (norm_nonneg _) K.coe_nonneg) le_rfl),
  apply C_adm.res_norm_noninc,
end

end scale_index

end system_of_complexes

namespace thm95

def rescale_functor' : ℕ → ((ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) ⥤ (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup))
| 0     := 𝟭 _
| 1     := 𝟭 _
| (m+2) := (whiskering_right _ _ _).obj (SemiNormedGroup.rescale (m+2)!)

instance rescale_functor'.additive : Π m, (rescale_functor' m).additive
| 0     := functor.id.additive
| 1     := functor.id.additive
| (m+2) := {}

def to_rescale' (r : ℝ≥0) [fact (0 < r)] :
  𝟭 (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) ⟶ ((whiskering_right _ _ _).obj (SemiNormedGroup.rescale r)) :=
{ app := λ V,
  { app := λ c, (SemiNormedGroup.to_rescale r).app _,
    naturality' := by { intros c₁ c₂ h, dsimp, ext i : 2, refl } },
  naturality' := λ C₁ C₂ f, by { ext, refl } }

@[simps app]
def scale' (i j : ℝ≥0) [fact (0 < i)] [fact (0 < j)] :
  ((whiskering_right ℝ≥0ᵒᵖ _ _).obj (SemiNormedGroup.rescale i)) ⟶
  ((whiskering_right ℝ≥0ᵒᵖ _ _).obj (SemiNormedGroup.rescale j)) :=
(whiskering_right ℝ≥0ᵒᵖ _ _).map $ SemiNormedGroup.scale i j

def rescale_nat_trans' : Π i j, rescale_functor' i ⟶ rescale_functor' j
| 0     1     := 𝟙 _
| 1     (j+2) := to_rescale' (j+2)!
| (i+2) (j+2) := scale' (i+2)! (j+2)!
| _     _     := 0

end thm95
