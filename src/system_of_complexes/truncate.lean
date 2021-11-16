import category_theory.preadditive.additive_functor

import system_of_complexes.basic

/-!

# Truncation

In this file we define a truncation functors for (systems of) complexes of seminormed groups.
This operation takes a complex `C` indexed by `ℕ`, and creates a new complex whose objects are
* in degree `0`:   the cokernel of `d : C 0 ⟶ C 1`
* in degree `n+1`: the object `C (n+2)`

Various lemmas are proved about how this construction preserves or reflects
various notions of bounded exactness.

-/

universes u

noncomputable theory
open_locale nnreal

open category_theory category_theory.limits

namespace SemiNormedGroup
open quotient_add_group

namespace truncate

variables (C : cochain_complex SemiNormedGroup.{u} ℕ)

open category_theory.preadditive

def X : ℕ → SemiNormedGroup.{u}
| 0     := explicit_cokernel (C.d 0 1)
| (n+1) := C.X (n+2)

def d : Π i j, X C i ⟶ X C j
| 0     1     := explicit_cokernel_desc (C.d_comp_d 0 1 2)
| (i+1) (j+1) := C.d (i+2) (j+2)
| _     _     := 0

lemma d_eq_zero : ∀ ⦃i j : ℕ⦄, ¬(complex_shape.up ℕ).rel i j → d C i j = 0
| 0     0     h := rfl
| 0     (j+2) h := rfl
| (i+1) 0     h := rfl
| 0     1     h := (h rfl).elim
| (i+1) (j+1) h := C.shape _ _ $ λ H, h $ nat.succ_injective $ H

lemma d_comp_d : Π i j k, i + 1 = j → j + 1 = k → d C i j ≫ d C j k = 0
| 0     1     2     rfl rfl := explicit_cokernel_desc_comp_eq_zero _ (C.d_comp_d _ _ _)
| (i+1) (j+1) (k+1) rfl rfl := C.d_comp_d _ _ _

@[simps]
def obj : cochain_complex SemiNormedGroup ℕ :=
{ X := X C,
  d := d C,
  shape' := d_eq_zero C,
  d_comp_d' := d_comp_d C }

lemma obj_d_add_one (C : cochain_complex SemiNormedGroup ℕ) (i j : ℕ) :
  (obj C).d (i+1) (j+1) = d C (i+1) (j+1) :=
rfl

def map_f {C₁ C₂ : cochain_complex SemiNormedGroup ℕ} (f : C₁ ⟶ C₂) :
  Π i:ℕ, X C₁ i ⟶ X C₂ i
| 0     := explicit_cokernel.map (f.comm 0 1).symm
| (i+1) := f.f (i+2)

lemma map_comm {C₁ C₂ : cochain_complex SemiNormedGroup.{u} ℕ} (f : C₁ ⟶ C₂) :
  Π i j, i + 1 = j → map_f f i ≫ d C₂ i j = d C₁ i j ≫ map_f f j
| 0     1     rfl := (explicit_coker.map_desc (f.comm 1 2).symm).symm
| (i+1) (j+1) rfl := f.comm (i+2) (j+2)

@[simps]
def map {C₁ C₂ : cochain_complex SemiNormedGroup.{u} ℕ} (f : C₁ ⟶ C₂) :
  obj C₁ ⟶ obj C₂ :=
{ f := map_f f,
  comm' := map_comm f }

end truncate

@[simps]
def truncate : cochain_complex SemiNormedGroup.{u} ℕ ⥤ cochain_complex SemiNormedGroup.{u} ℕ :=
{ obj := λ C, truncate.obj C,
  map := λ C₁ C₂ f, truncate.map f,
  map_id' := λ C, by ext (n|n) ⟨x⟩; refl,
  map_comp' := λ C₁ C₂ C₃ f g, by ext (n|n) ⟨x⟩; refl }

instance truncate.additive : truncate.additive :=
{ map_add' := by { intros, ext (n|n) ⟨⟩; refl } }

end SemiNormedGroup

namespace system_of_complexes

open category_theory

variables (C : system_of_complexes.{u})

@[simps]
def truncate : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ SemiNormedGroup.truncate

@[simp] lemma truncate_obj_d_zero_one (c : ℝ≥0) (y : C c 1) :
  (truncate.obj C).d 0 1 (SemiNormedGroup.explicit_cokernel_π _ y) = C.d 1 2 y := rfl

@[simp] lemma truncate_obj_d_succ_succ (c : ℝ≥0) (i j : ℕ) (x: truncate.obj C c (i+1)) :
  (truncate.obj C).d (i+1) (j+1) x = C.d (i+2) (j+2) x := rfl

lemma truncate_admissible (hC : C.admissible) :
  (truncate.obj C).admissible :=
{ d_norm_noninc' :=
  begin
    rintro c (i|i) j rfl,
    { apply SemiNormedGroup.explicit_cokernel_desc_norm_noninc,
      exact hC.d_norm_noninc _ _ 1 2 },
    { exact hC.d_norm_noninc _ _ (i+2) (i+3) }
  end,
  res_norm_noninc :=
  begin
    rintro c₁ c₂ (i|i) h x,
    { apply SemiNormedGroup.explicit_cokernel_desc_norm_noninc _,
      exact (SemiNormedGroup.norm_noninc_explicit_cokernel_π _).comp (hC.res_norm_noninc _ _ _ _) },
    { exact hC.res_norm_noninc _ _ _ _ x }
  end }

variables {k K : ℝ≥0} (m' m : ℕ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0)
include hk

lemma truncate_is_weak_bounded_exact (hC : C.is_weak_bounded_exact k K (m+1) c₀) :
  (truncate.obj C).is_weak_bounded_exact k K m c₀
| c hc 0 hi x ε hε :=
begin
  let π := λ c, SemiNormedGroup.explicit_cokernel_π (@d C c 0 1),
  obtain ⟨x, rfl⟩ : ∃ x', π _ x' = x := SemiNormedGroup.explicit_cokernel_π_surjective x,
  obtain ⟨i₀, -, hi₀, rfl, y, hy⟩ := hC c hc _ (nat.succ_le_succ hi) x ε hε,
  obtain rfl : i₀ = 0, { rwa nat.sub_self at hi₀ }, clear hi,
  refine ⟨0, _, rfl, rfl, 0, _⟩,
  simp only [normed_group_hom.map_zero, sub_zero,
    normed_group_hom.map_neg, truncate_obj_d_zero_one, norm_neg],
  calc _ = ∥π c (res x - C.d 0 1 y)∥ : _
  ... ≤ ∥res x - C.d 0 1 y∥ : SemiNormedGroup.norm_noninc_explicit_cokernel_π _ _
  ... ≤ _ : hy,
  have hπy : π c (C.d 0 1 y) = 0,
  { show (C.d 0 1 ≫ π c) y = 0, rw [SemiNormedGroup.comp_explicit_cokernel_π], refl },
  simp only [normed_group_hom.map_sub, hπy, sub_zero], refl
end
| c hc (i+1) hi x ε hε :=
begin
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc _ (nat.succ_le_succ hi) x ε hε,
  refine ⟨i, _, rfl, rfl, _⟩,
  cases i; [exact ⟨SemiNormedGroup.explicit_cokernel_π _ y, hy⟩, exact ⟨y, hy⟩],
end

lemma is_weak_bounded_exact_of_truncate (IH : C.is_weak_bounded_exact k K m c₀)
  (hC : (truncate.obj C).is_weak_bounded_exact k K m c₀) :
  C.is_weak_bounded_exact k K (m+1) c₀
| c hc 0 hi x ε hε := IH c hc 0 (nat.zero_le _) x ε hε
| c hc 1 hi x ε hε :=
begin
  let π := λ c, SemiNormedGroup.explicit_cokernel_π (@d C c 0 1),
  let δ := ε / 2,
  have hδε : δ + δ = ε, { dsimp [δ], rw [← add_div, half_add_self] },
  have hδ : 0 < δ := div_pos hε zero_lt_two,
  obtain ⟨x', Hxx', Hx'⟩ : ∃ x', π c x' = π c (res x) ∧ ∥x'∥ < ∥π c (res x)∥ + δ :=
    (SemiNormedGroup.is_quotient_explicit_cokernel_π _).norm_lift hδ _,
  obtain ⟨y, hy⟩ : ∃ y : C c 0, C.d 0 1 y = res x - x',
  { erw [quotient_add_group.eq, add_comm, ← sub_eq_add_neg, set.mem_range] at Hxx',
    exact Hxx' },
  obtain ⟨_, _, rfl, rfl, y', H⟩ := hC c hc _ (nat.zero_le m) (π _ x) δ hδ,
  refine ⟨0, 2, rfl, rfl, y, _⟩,
  simp only [d_self_apply, normed_group_hom.map_zero, sub_zero,
    truncate_obj_d_zero_one, norm_neg] at H ⊢,
  calc ∥res x - (C.d 0 1) y∥ ≤ ∥x'∥ : by rw [hy, sub_sub_cancel]
  ... ≤ ∥π c (res x)∥ + δ : Hx'.le
  ... ≤ ↑K * ∥C.d 1 2 x∥ + δ + δ : add_le_add_right H _
  ... ≤ ↑K * ∥C.d 1 2 x∥ + ε : by rw [add_assoc, hδε]
end
| c hc (i+2) hi x ε hε :=
begin
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc (i+1) (nat.pred_le_pred hi) x ε hε,
  refine ⟨i+1, _, rfl, rfl, _⟩,
  cases i,
  { let π := λ c, SemiNormedGroup.explicit_cokernel_π (@d C c 0 1),
    obtain ⟨y, rfl⟩ : ∃ y', π _ y' = y := SemiNormedGroup.explicit_cokernel_π_surjective y,
    exact ⟨y, hy⟩ },
  { exact ⟨y, hy⟩ },
end

lemma truncate_is_weak_bounded_exact_iff (hC : C.is_weak_bounded_exact k K m c₀) :
  (truncate.obj C).is_weak_bounded_exact k K m c₀ ↔ C.is_weak_bounded_exact k K (m+1) c₀ :=
⟨is_weak_bounded_exact_of_truncate C m c₀ hC, truncate_is_weak_bounded_exact C m c₀⟩

omit hk

end system_of_complexes
