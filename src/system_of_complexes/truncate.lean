import for_mathlib.normed_group_quotient
import for_mathlib.additive_functor

import system_of_complexes.basic
import locally_constant.Vhat -- preadditive category NormedGroup

/-!
# Truncation

In this file we define a truncation functors for (systems of) complexes of normed groups.
This operation takes a complex `C` indexed by `ℕ`, and creates a new complex whose objects are
* in degree `0`:   the cokernel of `d : C 0 ⟶ C 1`
* in degree `n+1`: the object `C (n+2)`

-/

universes u

noncomputable theory
open_locale nnreal

open category_theory category_theory.limits

namespace NormedGroup
open quotient_add_group

namespace truncate

variables (C : cochain_complex ℕ NormedGroup.{u})

open category_theory.preadditive

def X : ℕ → NormedGroup.{u}
| 0     := coker (C.d 0 1)
| (n+1) := C.X (n+2)

def d : Π i j, X C i ⟶ X C j
| 0     1     := coker.lift (C.d_comp_d 0 1 2)
| (i+1) (j+1) := C.d (i+2) (j+2)
| _     _     := 0

lemma d_eq_zero : ∀ ⦃i j : ℕ⦄, ¬differential_object.coherent_indices tt i j → d C i j = 0
| 0     0     h := rfl
| 0     (j+2) h := rfl
| (i+1) 0     h := rfl
| 0     1     h := (h dec_trivial).elim
| (i+1) (j+1) h := C.d_eq_zero $ λ H, h $ nat.succ_injective $ H

lemma d_comp_d : Π i j k, d C i j ≫ d C j k = 0
| 0     1     2     := coker.lift_comp_eq_zero _ (C.d_comp_d _ _ _)
| (i+1) (j+1) (k+1) := C.d_comp_d _ _ _
| 0     0     _     := zero_comp
| 0     (j+2) _     := zero_comp
| (i+1) 0     _     := zero_comp
| 0     1     0     := comp_zero
| (i+1) (j+1) 0     := comp_zero
| 0     1     1     := by { rw [@d_eq_zero C 1, comp_zero], dec_trivial }
| 0     1     (k+3) := by { rw [@d_eq_zero C 1, comp_zero], dec_trivial }

@[simps]
def obj : cochain_complex ℕ NormedGroup :=
{ X := X C,
  d := d C,
  d_comp_d := d_comp_d C,
  d_eq_zero := d_eq_zero C }

lemma obj_d_add_one (C : cochain_complex ℕ NormedGroup) (i j : ℕ) :
  (obj C).d (i+1) (j+1) = d C (i+1) (j+1) :=
rfl

def map_f {C₁ C₂ : cochain_complex ℕ NormedGroup} (f : C₁ ⟶ C₂) :
  Π i:ℕ, X C₁ i ⟶ X C₂ i
| 0     := coker.map (f.comm 0 1)
| (i+1) := f.f (i+2)

lemma map_comm {C₁ C₂ : cochain_complex ℕ NormedGroup.{u}} (f : C₁ ⟶ C₂) :
  Π i j, d C₁ i j ≫ map_f f j = map_f f i ≫ d C₂ i j
| 0     1     := coker.map_lift_comm (f.comm 1 2)
| (i+1) (j+1) := f.comm (i+2) (j+2)
| 0     0     := by { rw [d_eq_zero, d_eq_zero, zero_comp, comp_zero]; dec_trivial }
| 0     (j+2) := by { rw [d_eq_zero, d_eq_zero, zero_comp, comp_zero]; dec_trivial }
| (i+1) 0     := by { rw [d_eq_zero, d_eq_zero, zero_comp, comp_zero]; dec_trivial }

@[simps]
def map {C₁ C₂ : cochain_complex ℕ NormedGroup.{u}} (f : C₁ ⟶ C₂) :
  obj C₁ ⟶ obj C₂ :=
{ f := map_f f,
  comm := map_comm f }

end truncate

@[simps]
def truncate : cochain_complex ℕ NormedGroup.{u} ⥤ cochain_complex ℕ NormedGroup.{u} :=
{ obj := λ C, truncate.obj C,
  map := λ C₁ C₂ f, truncate.map f,
  map_id' := λ C, by ext (n|n) ⟨x⟩; refl,
  map_comp' := λ C₁ C₂ C₃ f g, by ext (n|n) ⟨x⟩; refl }

instance truncate.additive : truncate.additive :=
{ map_zero' := by { intros, ext (n|n) ⟨⟩; refl },
  map_add' := by { intros, ext (n|n) ⟨⟩; refl } }

end NormedGroup

namespace system_of_complexes

open differential_object category_theory

variables (C : system_of_complexes.{u})

@[simps]
def truncate : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ NormedGroup.truncate

@[simp] lemma truncate_obj_d_zero_one (c : ℝ≥0) (y : C c 1) :
  (truncate.obj C).d 0 1 (NormedGroup.coker.π y) = C.d 1 2 y := rfl

@[simp] lemma truncate_obj_d_succ_succ (c : ℝ≥0) (i j : ℕ) (x: truncate.obj C c (i+1)) :
  (truncate.obj C).d (i+1) (j+1) x = C.d (i+2) (j+2) x := rfl

lemma truncate_admissible (hC : C.admissible) :
  (truncate.obj C).admissible :=
{ d_norm_noninc' :=
  begin
    rintro c (i|i) j rfl,
    { apply NormedGroup.coker.lift_norm_noninc,
      exact hC.d_norm_noninc _ _ 1 2 },
    { exact hC.d_norm_noninc _ _ (i+2) (i+3) }
  end,
  res_norm_noninc :=
  begin
    rintro c₁ c₂ (i|i) h x,
    { apply NormedGroup.coker.lift_norm_noninc,
      exact NormedGroup.coker.π_norm_noninc.comp (hC.res_norm_noninc _ _ _ _) },
    { exact hC.res_norm_noninc _ _ _ _ x }
  end }

variables {k K : ℝ≥0} (m' m : ℕ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0)
include hk

lemma truncate_is_weak_bounded_exact (hC : C.is_weak_bounded_exact k K (m+1) c₀) :
  (truncate.obj C).is_weak_bounded_exact k K m c₀
| c hc 0 hi x ε hε :=
begin
  let π := λ c, @NormedGroup.coker.π _ _ (@d C c 0 1),
  obtain ⟨x, rfl⟩ : ∃ x', π _ x' = x := NormedGroup.coker.π_surjective x,
  obtain ⟨i₀, -, hi₀, rfl, y, hy⟩ := hC c hc _ (nat.succ_le_succ hi) x ε hε,
  obtain rfl : i₀ = 0, { rwa nat.sub_self at hi₀ }, clear hi,
  refine ⟨0, _, rfl, rfl, 0, _⟩,
  simp only [normed_group_hom.map_zero, sub_zero,
    normed_group_hom.map_neg, truncate_obj_d_zero_one, norm_neg],
  calc _ = ∥π c (res x - C.d 0 1 y)∥ : _
  ... ≤ ∥res x - C.d 0 1 y∥ : NormedGroup.coker.π_norm_noninc _
  ... ≤ _ : hy,
  have hπy : π c (C.d 0 1 y) = 0,
  { show (C.d 0 1 ≫ π c) y = 0, rw [NormedGroup.coker.comp_pi_eq_zero], refl },
  simp only [normed_group_hom.map_sub, hπy, sub_zero], refl
end
| c hc (i+1) hi x ε hε :=
begin
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc _ (nat.succ_le_succ hi) x ε hε,
  refine ⟨i, _, rfl, rfl, _⟩,
  cases i; [exact ⟨NormedGroup.coker.π y, hy⟩, exact ⟨y, hy⟩],
end

lemma is_weak_bounded_exact_of_truncate (IH : C.is_weak_bounded_exact k K m c₀)
  (hC : (truncate.obj C).is_weak_bounded_exact k K m c₀) :
  C.is_weak_bounded_exact k K (m+1) c₀
| c hc 0 hi x ε hε := IH c hc 0 (nat.zero_le _) x ε hε
| c hc 1 hi x ε hε :=
begin
  let π := λ c, @NormedGroup.coker.π _ _ (@d C c 0 1),
  let δ := ε / 2,
  have hδε : δ + δ = ε, { dsimp [δ], rw [← add_div, half_add_self] },
  have hδ : 0 < δ := div_pos hε zero_lt_two,
  let γ := δ / 2,
  have hγδ : γ + γ = δ, { dsimp [γ], rw [← add_div, half_add_self] },
  have hγ : 0 < γ := div_pos hδ zero_lt_two,
  obtain ⟨x', Hxx', Hx'⟩ : ∃ x', π c x' = π c (res x) ∧ ∥x'∥ < ∥π c (res x)∥ + γ :=
    normed_group_hom.quotient_norm_lift (NormedGroup.coker.π_is_quotient) hγ _,
  obtain ⟨y, hy⟩ : ∃ y : C c 0, ∥res x - (C.d 0 1) y∥ ≤ ∥x'∥ + γ :=
    NormedGroup.coker.exists_norm_le _ _ Hxx'.symm γ hγ,
  obtain ⟨_, _, rfl, rfl, y', H⟩ := hC c hc _ (nat.zero_le m) (π _ x) δ hδ,
  refine ⟨0, 2, rfl, rfl, y, _⟩,
  simp only [d_self_apply, normed_group_hom.map_zero, sub_zero,
    truncate_obj_d_zero_one, norm_neg] at H ⊢,
  calc ∥res x - (C.d 0 1) y∥ ≤ ∥x'∥ + γ : hy
  ... ≤ ∥π c (res x)∥ + γ + γ : add_le_add_right Hx'.le _
  ... ≤ ∥π c (res x)∥ + δ : by rw [add_assoc, hγδ]
  ... ≤ ↑K * ∥C.d 1 2 x∥ + δ + δ : add_le_add_right H _
  ... ≤ ↑K * ∥C.d 1 2 x∥ + ε : by rw [add_assoc, hδε]
end
| c hc (i+2) hi x ε hε :=
begin
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc (i+1) (nat.pred_le_pred hi) x ε hε,
  refine ⟨i+1, _, rfl, rfl, _⟩,
  cases i,
  { let π := λ c, @NormedGroup.coker.π _ _ (@d C c 0 1),
    obtain ⟨y, rfl⟩ : ∃ y', π _ y' = y := NormedGroup.coker.π_surjective y,
    exact ⟨y, hy⟩ },
  { exact ⟨y, hy⟩ },
end

lemma truncate_is_weak_bounded_exact_iff (hC : C.is_weak_bounded_exact k K m c₀) :
  (truncate.obj C).is_weak_bounded_exact k K m c₀ ↔ C.is_weak_bounded_exact k K (m+1) c₀ :=
⟨is_weak_bounded_exact_of_truncate C m c₀ hC, truncate_is_weak_bounded_exact C m c₀⟩

omit hk

end system_of_complexes
