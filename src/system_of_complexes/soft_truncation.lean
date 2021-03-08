import for_mathlib.normed_group_quotient

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

def d (C : cochain_complex ℤ NormedGroup.{u}) :
  Π i:ℤ, X C i ⟶ X C (i+1)
| -[1+n]  := 0
| 0       := coker.lift (C.d_comp_d (-1) 0 1)
| (n+1:ℕ) := C.d (n+1) (n+1+1)

lemma d2 (C : cochain_complex ℤ NormedGroup.{u}) :
  Π i:ℤ, d C i ≫ d C (i+1) = 0
| -[1+n]  := show 0 ≫ _ = 0, by rw zero_comp
| 0       := coker.lift_comp_eq_zero _ (C.d_comp_d _ _ _)
| (n+1:ℕ) := C.d_comp_d (n+1) _ _

@[simps]
def obj (C : cochain_complex ℤ NormedGroup.{u}) :
  cochain_complex ℤ NormedGroup :=
{ X := X C,
  differential := d C,
  differential2 := by { dsimp, rintro i _ rfl, simpa using d2 C i } }

def map_f {C₁ C₂ : cochain_complex ℤ NormedGroup.{u}} (f : C₁ ⟶ C₂) :
  Π i:ℤ, X C₁ i ⟶ X C₂ i
| -[1+n]  := 0
| 0       := coker.map (cochain_complex.hom.comm f (-1) 0)
| (n+1:ℕ) := f.f (n+1)

lemma map_comm {C₁ C₂ : cochain_complex ℤ NormedGroup.{u}} (f : C₁ ⟶ C₂) :
  Π i:ℤ, d C₁ i ≫ map_f f (i+1) = map_f f i ≫ d C₂ i
| -[1+n]  := show 0 ≫ _ = _ ≫ 0, by rw [zero_comp, comp_zero]
| 0       := coker.map_lift_comm (cochain_complex.hom.comm f 0 1)
| (n+1:ℕ) := cochain_complex.hom.comm f (n+1) _

def map {C₁ C₂ : cochain_complex ℤ NormedGroup.{u}} (f : C₁ ⟶ C₂) :
  obj C₁ ⟶ obj C₂ :=
{ f := map_f f,
  comm' := map_comm f }

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

end NormedGroup

namespace system_of_complexes

variables (C : system_of_complexes)

@[simps]
def soft_truncation' : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ NormedGroup.soft_truncation'

lemma soft_truncation'_d_neg (c : ℝ≥0) (i j : ℤ) (hi : i < 0) :
  ((soft_truncation'.obj C).d i j : (soft_truncation'.obj C) c i ⟶ _) = 0 :=
begin
  cases i,
  { refine (not_le.mpr hi $ int.coe_zero_le i).elim },
  dsimp [system_of_complexes.d, cochain_complex.d, differential_object.d],
  split_ifs with h,
  { cases h, dsimp [differential_object.d_aux], simp only [category.comp_id], refl },
  { refl }
end

variables (k K : ℝ≥0) (m : ℤ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0)
include hk

lemma soft_truncation'_is_bounded_exact (hC : C.is_bounded_exact k K m c₀) :
  (soft_truncation'.obj C).is_bounded_exact k K m c₀ :=
begin
  rintros c hc ((i|i)|i) hi,
  { sorry },
  { intro x,
    obtain ⟨i', j, hi', rfl, y, hy⟩ := hC c hc _ hi x,
    refine ⟨i', _, hi', rfl, _⟩,
    simp at hi', subst i',
    cases i,
    { sorry },
    { refine ⟨y, _⟩,
      dsimp at hy ⊢, sorry } },
  { intro x,
    refine ⟨-[1+ i.succ], _, rfl, rfl, 0, _⟩,
    calc _ = 0 : _
       ... ≤ _ : _,
    { rw norm_eq_zero, ext },
    { refine mul_nonneg K.2 (norm_nonneg _) } }
end

lemma soft_truncation'_is_bounded_exact_iff (hC : C.is_bounded_exact k K 0 c₀) :
  (soft_truncation'.obj C).is_bounded_exact k K m c₀ ↔ C.is_bounded_exact k K m c₀ :=
begin
  apply forall_congr, intros c,
  apply forall_congr, intros hc,
  apply forall_congr, intros i,
  apply forall_congr, intros hi,
  sorry
end

lemma soft_truncation'_is_weak_bounded_exact_iff (hC : C.is_weak_bounded_exact k K 0 c₀) :
  (soft_truncation'.obj C).is_weak_bounded_exact k K m c₀ ↔ C.is_weak_bounded_exact k K m c₀ :=
sorry

omit hk

-- move this
def functor.has_shift (C D : Type*) [category C] [category D] [has_shift D] :
  has_shift (C ⥤ D) := ⟨(shift _).congr_right⟩

instance : has_shift system_of_complexes.{u} :=
functor.has_shift (ℝ≥0ᵒᵖ) (cochain_complex ℤ NormedGroup)

-- this is probably way too much defeq abuse
lemma shift_d (c : ℝ≥0) (i j : ℤ) : @d (C⟦1⟧) c i j = C.d (i+1) (j+1) :=
begin
  by_cases h : i + 1 = j,
  swap, { rw [d_eq_zero _ _ _ _ h, d_eq_zero], rwa [ne.def, add_left_inj] },
  dsimp [d, cochain_complex.d, differential_object.d],
  rw [dif_pos, dif_pos],
  swap, { rwa ← add_left_inj (1:ℤ) at h },
  swap, { exact h },
  dsimp [differential_object.d_aux],
  congr' 1,
  sorry
end

include hk

lemma shift_is_bounded_exact_aux (hC : C.is_bounded_exact k K m c₀) :
  C⟦1⟧.is_bounded_exact k K (m - 1) c₀ :=
begin
  intros c hc i hi,
  rintro (x : C (k*c) (i+1)),
  obtain ⟨i', _, hi', rfl, y, hy⟩ := hC c hc (i + 1) (by linarith) x,
  rw add_left_inj at hi', subst i',
  obtain ⟨i, rfl⟩ : ∃ n, n + 1 = i := ⟨i - 1, sub_add_cancel i 1⟩,
  refine ⟨_, _, rfl, rfl, y, _⟩,
  simpa only [shift_d],
end

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
