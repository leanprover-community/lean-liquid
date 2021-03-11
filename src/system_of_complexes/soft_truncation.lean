import for_mathlib.normed_group_quotient
import for_mathlib.additive_functor

import system_of_complexes.basic
import locally_constant.Vhat -- preadditive category NormedGroup

/-!
# Soft truncation

In this file we define soft truncation functors
for (systems of) complexes of normed groups.

We call these `soft_truncation'` to distinguish them from the usual soft truncation functors.
The difference is solely in the definition of the object in degree `0`.
Usually this object is defined as `C 0` modulo the kernel of `d : C 0 ⟶ C 1`.
Instead, we define it as `C 0` modulo the image of `d : C (-1) ⟶ C 0`.
Hence the two definitions agree iff `C` is exact in degree `0`.

-/

universes u

noncomputable theory
open_locale nnreal

open category_theory category_theory.limits

namespace NormedGroup
open quotient_add_group

namespace soft_truncation'

-- Note: the next sorry needs a `NormedGroup`, so we need to bundle.
def X (C : cochain_complex ℤ NormedGroup.{u}) : ℤ → NormedGroup.{u}
| -[1+n]  := 0
| 0       := coker (C.d (-1) 0)
| (n+1:ℕ) := C.X (n+1)

def d (C : cochain_complex ℤ NormedGroup) :
  Π i:ℤ, X C i ⟶ X C (i+1)
| -[1+n]  := 0
| 0       := coker.lift (C.d_comp_d (-1) 0 1)
| (n+1:ℕ) := C.d (n+1) (n+1+1)

lemma d_comp_d (C : cochain_complex ℤ NormedGroup) :
  Π i:ℤ, d C i ≫ d C (i+1) = 0
| -[1+n]  := show 0 ≫ _ = 0, by rw zero_comp
| 0       := coker.lift_comp_eq_zero _ (C.d_comp_d _ _ _)
| (n+1:ℕ) := C.d_comp_d (n+1) _ _

@[simps]
def obj (C : cochain_complex ℤ NormedGroup) :
  cochain_complex ℤ NormedGroup :=
cochain_complex.mk' (X C) (d C) (d_comp_d C)

lemma obj_d_add_one (C : cochain_complex ℤ NormedGroup) (i : ℤ) :
  (obj C).d i (i + 1) = d C i :=
cochain_complex.mk'_d' _ _ _ _

@[simp] lemma obj_X_neg_one (C : cochain_complex ℤ NormedGroup) :
  (obj C).X (-1) = 0 := rfl

def map_f {C₁ C₂ : cochain_complex ℤ NormedGroup} (f : C₁ ⟶ C₂) :
  Π i:ℤ, X C₁ i ⟶ X C₂ i
| -[1+n]  := 0
| 0       := coker.map (f.comm (-1) 0)
| (n+1:ℕ) := f.f (n+1)

lemma map_comm {C₁ C₂ : cochain_complex ℤ NormedGroup.{u}} (f : C₁ ⟶ C₂) :
  Π i:ℤ, d C₁ i ≫ map_f f (i+1) = map_f f i ≫ d C₂ i
| -[1+n]  := show 0 ≫ _ = _ ≫ 0, by rw [zero_comp, comp_zero]
| 0       := coker.map_lift_comm (f.comm 0 1)
| (n+1:ℕ) := f.comm (n+1) _

@[simps]
def map {C₁ C₂ : cochain_complex ℤ NormedGroup.{u}} (f : C₁ ⟶ C₂) :
  obj C₁ ⟶ obj C₂ :=
{ f := map_f f,
  comm :=
  begin
    intros i j,
    show (obj C₁).d i j ≫ map_f f j = map_f f i ≫ (obj C₂).d i j,
    dsimp,
    split_ifs with h,
    { subst h, exact map_comm f _ },
    { rw [zero_comp, comp_zero] }
  end }

end soft_truncation'

@[simps]
def soft_truncation' : cochain_complex ℤ NormedGroup.{u} ⥤ cochain_complex ℤ NormedGroup.{u} :=
{ obj := λ C, soft_truncation'.obj C,
  map := λ C₁ C₂ f, soft_truncation'.map f,
  map_id' := λ C,
  begin
    ext ((n|n)|n) : 2,
    { ext x, induction x, refl, refl },
    { refl },
    { ext }
  end,
  map_comp' := λ C₁ C₂ C₃ f g,
  begin
    ext ((n|n)|n) : 2,
    { ext x, induction x, refl, refl },
    { refl },
    { ext }
  end }
.

@[simp] lemma soft_truncation'_obj_X_neg_one (C : cochain_complex ℤ NormedGroup) :
  (soft_truncation'.obj C).X (-1) = 0 := rfl

instance soft_truncation'.additive : soft_truncation'.additive :=
{ map_zero' := by { intros, ext ((n|n)|n) : 2, { ext ⟨⟩, refl }, { refl }, { refl } },
  map_add' := by { intros, ext ((n|n)|n) : 2, { ext ⟨⟩, refl }, { refl }, { refl } } }

open differential_object

@[simps]
def shift_and_truncate : cochain_complex ℤ NormedGroup ⥤ cochain_complex ℤ NormedGroup :=
(complex_like.shift _ _) ⋙ soft_truncation'

instance shift_and_truncate.additive : shift_and_truncate.additive :=
@functor.additive.comp _ _ _ _ _ _ _ _ _ _ _ _ soft_truncation'.additive
-- TODO: why can Lean not find `soft_truncation'.additive` via TC?

end NormedGroup

namespace system_of_complexes

open differential_object category_theory

variables (C : system_of_complexes.{u})

@[simps]
def soft_truncation' : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ NormedGroup.soft_truncation'

@[simps]
def shift : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ (complex_like.shift _ _)

@[simps]
def shift_and_truncate : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ NormedGroup.shift_and_truncate

@[simps]
def shift_comp_soft_truncation' : shift ⋙ soft_truncation' ≅ shift_and_truncate :=
nat_iso.of_components (λ X, nat_iso.of_components (λ c, eq_to_iso rfl) $
  by { intros c₁ c₂ h, dsimp, simp only [category.id_comp, category.comp_id], refl }) $
  by { intros X Y f, ext, dsimp, simp only [category.id_comp, category.comp_id], refl }
.

lemma shift_d (c : ℝ≥0) (i j : ℤ) : (shift.obj C).d i j = -@d C c (i + 1) (j + 1) :=
rfl

@[simp] lemma soft_truncation'_X_neg_one (c : ℝ≥0) :
  (soft_truncation'.obj C) c (-1) = 0 := rfl

lemma soft_truncation'_d_neg (c : ℝ≥0) (i j : ℤ) (hi : i < 0) :
  ((soft_truncation'.obj C).d i j : (soft_truncation'.obj C) c i ⟶ _) = 0 :=
begin
  cases i,
  { refine (not_le.mpr hi $ int.coe_zero_le i).elim },
  dsimp [system_of_complexes.d],
  split_ifs with h,
  { subst j, simp only [eq_to_hom_refl, category.comp_id], refl },
  { refl }
end

variables {k K : ℝ≥0} (m' m : ℤ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0)
include hk

lemma soft_truncation'_is_weak_bounded_exact (hC : C.is_weak_bounded_exact k K m c₀) :
  (soft_truncation'.obj C).is_weak_bounded_exact k K m c₀
| c hc (0:ℕ)   hi x ε hε :=
begin
  let π := λ c, @NormedGroup.coker.π _ _ (@d C c (-1) 0),
  obtain ⟨x, rfl⟩ : ∃ x', π _ x' = x := NormedGroup.coker.π_surjective x,
  obtain ⟨i', j, hi', rfl, y, hy⟩ := hC c hc _ hi x ε hε,
  obtain rfl : i' = -1, { rwa ← eq_sub_iff_add_eq at hi' },
  refine ⟨-1, _, rfl, rfl, 0, _⟩,
  simp only [normed_group_hom.map_zero, sub_zero],
  calc _ = ∥π c (res x - C.d (-1) 0 y)∥ : _
  ... ≤ ∥res x - C.d _ 0 y∥ : normed_group_hom.quotient_norm_le (NormedGroup.coker.π_is_quotient) _
  ... ≤ _ : hy,
  congr' 1,
  have hπy : π c (C.d _ 0 y) = 0,
  { show (C.d _ 0 ≫ π c) y = 0, rw [NormedGroup.coker.comp_pi_eq_zero], refl },
  simp only [normed_group_hom.map_sub, hπy, sub_zero], refl,
end
| c hc (1:ℕ)   hi x ε hε :=
begin
  obtain ⟨i', j, hi', rfl, y, hy⟩ := hC c hc _ hi x ε hε,
  simp at hi', subst i',
  exact ⟨0, _, rfl, rfl, NormedGroup.coker.π y, hy⟩
end
| c hc (i+2:ℕ) hi x ε hε :=
begin
  obtain ⟨i', j, hi', rfl, y, hy⟩ := hC c hc _ hi x ε hε,
  simp at hi', subst i',
  refine ⟨i+1, _, rfl, rfl, y, _⟩, dsimp [d, soft_truncation'],
  simpa only [if_true, eq_self_iff_true, category.comp_id] using hy
end
| c hc -[1+i]  hi x ε hε :=
begin
  refine ⟨-[1+ i.succ], _, rfl, rfl, 0, _⟩,
  transitivity' 0,
  { apply le_of_eq, rw norm_eq_zero, ext },
  { refine add_nonneg (mul_nonneg K.2 (norm_nonneg _)) (le_of_lt hε) }
end

lemma is_weak_bounded_exact_of_soft_truncation'
  (hC : (soft_truncation'.obj C).is_weak_bounded_exact k K m c₀)
  (hneg : C.is_weak_bounded_exact k K (-1) c₀) :
  C.is_weak_bounded_exact k K m c₀
| c hc (0:ℕ)   hi x ε hε :=
begin
  let π := λ c, @NormedGroup.coker.π _ _ (@d C c (-1) 0),
  let δ := ε / 2,
  have hδε : δ + δ = ε, { dsimp [δ], rw [← add_div, half_add_self] },
  have hδ : 0 < δ := div_pos hε zero_lt_two,
  let γ := δ / 2,
  have hγδ : γ + γ = δ, { dsimp [γ], rw [← add_div, half_add_self] },
  have hγ : 0 < γ := div_pos hδ zero_lt_two,
  obtain ⟨x', Hxx', Hx'⟩ : ∃ x', π c x' = π c (res x) ∧ ∥x'∥ < ∥π c (res x)∥ + γ :=
    normed_group_hom.quotient_norm_lift (NormedGroup.coker.π_is_quotient) hγ _,
  obtain ⟨y, hy⟩ : ∃ y : C c (-1), ∥res x - (C.d (-1) ↑0) y∥ ≤ ∥x'∥ + γ,
  { sorry },
  obtain ⟨i', j, hi', rfl, y', H⟩ := hC c hc _ hi (π _ x) δ hδ,
  obtain rfl : i' = -1, { rwa ← eq_sub_iff_add_eq at hi' },
  obtain rfl : y' = 0, { cases y', refl },
  refine ⟨-1, 1, rfl, rfl, y, _⟩,
  simp only [normed_group_hom.map_zero, sub_zero] at H ⊢,
  calc ∥res x - (C.d (-1) ↑0) y∥ ≤ ∥x'∥ + γ : hy
  ... ≤ ∥π c (res x)∥ + γ + γ : add_le_add_right Hx'.le _
  ... ≤ ∥π c (res x)∥ + δ : by rw [add_assoc, hγδ]
  ... ≤ ↑K * ∥C.d ↑0 1 x∥ + δ + δ : add_le_add_right H _
  ... ≤ ↑K * ∥C.d ↑0 1 x∥ + ε : by rw [add_assoc, hδε]
end
| c hc (1:ℕ)   hi x ε hε :=
begin
  obtain ⟨i', j, hi', rfl, y, hy⟩ := hC c hc _ hi x ε hε,
  simp at hi', subst i',
  let π := λ c, @NormedGroup.coker.π _ _ (@d C c (-1) 0),
  obtain ⟨y, rfl⟩ : ∃ y', π _ y' = y := NormedGroup.coker.π_surjective y,
  exact ⟨0, _, rfl, rfl, y, hy⟩
end
| c hc (i+2:ℕ) hi x ε hε :=
begin
  obtain ⟨i', j, hi', rfl, y, hy⟩ := hC c hc _ hi x ε hε,
  simp at hi', subst i',
  refine ⟨i+1, _, rfl, rfl, y, _⟩, dsimp [d, soft_truncation'] at hy,
  simpa only [if_true, eq_self_iff_true, category.comp_id] using hy
end
| c hc -[1+i]  hi x ε hε :=
begin
  refine hneg c hc _ _ x ε hε,
  show -(i+1:ℤ) ≤ -1,
  apply neg_le_neg,
  simp only [int.coe_nat_nonneg, le_add_iff_nonneg_left]
end

lemma soft_truncation'_is_weak_bounded_exact_iff
  (hneg : C.is_weak_bounded_exact k K (-1) c₀) :
  (soft_truncation'.obj C).is_weak_bounded_exact k K m c₀ ↔ C.is_weak_bounded_exact k K m c₀ :=
begin
  split,
  { intro H, apply is_weak_bounded_exact_of_soft_truncation'; assumption },
  { intro H, apply soft_truncation'_is_weak_bounded_exact, exact H }
end

lemma shift_is_weak_bounded_exact_iff (h : m' + 1 = m) :
  (shift.obj C).is_weak_bounded_exact k K m' c₀ ↔ C.is_weak_bounded_exact k K m c₀ :=
begin
  apply forall_congr, intros c,
  apply forall_congr, intros hc,
  subst m,
  have aux : ∀ P : ℤ → Prop, (∀ i, i ≤ m' + 1 → P i) ↔ (∀ i, i ≤ m' → P (i+1)),
  { intro P, split; intros H i hi,
    { apply H, rwa add_le_add_iff_right },
    { rw ← sub_add_cancel i 1, apply H, rwa sub_le_iff_le_add } },
  rw aux, clear aux,
  apply forall_congr, intros i,
  have aux : ∀ P : ℤ → ℤ → Prop,
    (∃ (i' j : ℤ) (hi' : i' + 1 = i + 1) (hj : i + 1 + 1 = j), P i' j) ↔
    (∃ (i' j : ℤ) (hi' : i' + 1 = i) (hj : i + 1 = j), P (i' + 1) (j + 1)),
  { intro P,
    simp only [exists_prop, add_left_inj, exists_eq_left, exists_and_distrib_left, exists_eq_left'],
    split, { intro h, use [i-1], simpa using h }, { rintro ⟨_, rfl, h⟩, exact h } },
  simp only [aux], clear aux,
  simp only [exists_prop, exists_and_distrib_left, exists_eq_left'],
  apply forall_congr, intros hi,
  apply forall_congr, intros x,
  apply forall_congr, intros ε,
  apply forall_congr, intros hε,
  apply exists_congr, intros i',
  apply and_congr iff.rfl,
  simp only [shift_d],
  split;
  { rintro ⟨y, hy⟩, refine ⟨-y, _⟩,
    simpa only [sub_neg_eq_add, normed_group_hom.map_neg, normed_group_hom.coe_neg, pi.neg_apply,
      norm_neg, sub_neg_eq_add, ← sub_eq_add_neg] using hy }
end

lemma shift_and_truncate_is_weak_bounded_exact
  (hC : C.is_weak_bounded_exact k K m c₀) (h : m' + 1 = m) :
  (shift_and_truncate.obj C).is_weak_bounded_exact k K m' c₀ :=
begin
  rw ← is_weak_bounded_exact.iff_of_iso (shift_comp_soft_truncation'.{u u}.app C),
  { dsimp,
    apply soft_truncation'_is_weak_bounded_exact,
    rwa shift_is_weak_bounded_exact_iff _ _ _ _ h },
  { intros c i, exact isometry_id }
end

lemma shift_and_truncate_is_weak_bounded_exact_iff
  (h0 : C.is_weak_bounded_exact k K 0 c₀) (h : m' + 1 = m) :
  (shift_and_truncate.obj C).is_weak_bounded_exact k K m' c₀ ↔ C.is_weak_bounded_exact k K m c₀ :=
begin
  rw ← is_weak_bounded_exact.iff_of_iso (shift_comp_soft_truncation'.{u u}.app C),
  { dsimp,
    rw soft_truncation'_is_weak_bounded_exact_iff,
    { apply shift_is_weak_bounded_exact_iff, exact h },
    { rwa shift_is_weak_bounded_exact_iff, refl } },
  { intros c i, exact isometry_id }
end

omit hk

lemma shift_and_truncate_admissible (hC : C.admissible) :
  (shift_and_truncate.obj C).admissible :=
{ d_norm_noninc' := sorry,
  res_norm_noninc := sorry }








/- === Old cruft === -/

-- -- move this
-- def functor.has_shift (C D : Type*) [category C] [category D] [has_shift D] :
--   has_shift (C ⥤ D) := ⟨(shift _).congr_right⟩

/- === We only care about weak exactness. So the following code can probably be deleted. === -/

-- lemma soft_truncation'_is_bounded_exact (hC : C.is_bounded_exact k K m c₀) :
--   (soft_truncation'.obj C).is_bounded_exact k K m c₀ :=
-- begin
--   rintros c hc ((i|i)|i) hi,
--   { admit },
--   { intro x,
--     obtain ⟨i', j, hi', rfl, y, hy⟩ := hC c hc _ hi x,
--     refine ⟨i', _, hi', rfl, _⟩,
--     simp at hi', subst i',
--     cases i,
--     { admit },
--     { refine ⟨y, _⟩,
--       dsimp at hy ⊢, admit } },
--   { intro x,
--     refine ⟨-[1+ i.succ], _, rfl, rfl, 0, _⟩,
--     calc _ = 0 : _
--        ... ≤ _ : _,
--     { rw norm_eq_zero, ext },
--     { refine mul_nonneg K.2 (norm_nonneg _) } }
-- end

-- lemma soft_truncation'_is_bounded_exact_iff (hC : C.is_bounded_exact k K 0 c₀) :
--   (soft_truncation'.obj C).is_bounded_exact k K m c₀ ↔ C.is_bounded_exact k K m c₀ :=
-- begin
--   apply forall_congr, intros c,
--   apply forall_congr, intros hc,
--   apply forall_congr, intros i,
--   apply forall_congr, intros hi,
--   admit
-- end

-- don't think we want to use this
-- instance : has_shift system_of_complexes.{u} :=
-- functor.has_shift (ℝ≥0ᵒᵖ) (cochain_complex ℤ NormedGroup)

-- -- this is probably way too much defeq abuse
-- lemma shift_d (c : ℝ≥0) (i j : ℤ) : @d (C⟦1⟧) c i j = C.d (i+1) (j+1) :=
-- begin
--   by_cases h : i + 1 = j,
--   swap, { rw [d_eq_zero _ _ _ _ h, d_eq_zero], rwa [ne.def, add_left_inj] },
--   dsimp [d, cochain_complex.d, differential_object.d],
--   rw [dif_pos, dif_pos],
--   swap, { rwa ← add_left_inj (1:ℤ) at h },
--   swap, { exact h },
--   dsimp [differential_object.d_aux],
--   congr' 1,
--   sorry
-- end

-- include hk

-- lemma shift_is_bounded_exact_aux (hC : C.is_bounded_exact k K m c₀) :
--   C⟦1⟧.is_bounded_exact k K (m - 1) c₀ :=
-- begin
--   intros c hc i hi,
--   rintro (x : C (k*c) (i+1)),
--   obtain ⟨i', _, hi', rfl, y, hy⟩ := hC c hc (i + 1) (by linarith) x,
--   rw add_left_inj at hi', subst i',
--   obtain ⟨i, rfl⟩ : ∃ n, n + 1 = i := ⟨i - 1, sub_add_cancel i 1⟩,
--   refine ⟨_, _, rfl, rfl, y, _⟩,
--   simpa only [shift_d],
-- end

-- lemma shift_is_bounded_exact (hC : C.is_bounded_exact k K m c₀) :
--   ∀ (n : ℤ), C⟦n⟧.is_bounded_exact k K (m - n) c₀
-- | (0:ℕ)    := by simpa only [int.coe_nat_zero, sub_zero, equivalence.pow_zero]
-- | (1:ℕ)    :=
-- begin
-- end
-- | (n+1:ℕ)  := _
-- | -[1+0]   := _
-- | -[1+(n+1)] := _
-- begin
--   apply int.induction_on' n 0; clear n,
--   { simpa only [functor.id_obj, sub_zero, equivalence.pow_zero, equivalence.refl_functor] },
--   { intros n hn hC' c hc i hi x,
--     specialize hC' c hc (i + 1) (by linarith),
--      },
--   -- obtain ⟨i', j, hi', hj, y, hy⟩ := hC c hc (i - n),
-- end

end system_of_complexes
