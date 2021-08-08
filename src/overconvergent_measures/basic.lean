import analysis.specific_limits
import category_theory.Fintype
import analysis.normed_space.basic

import overconvergent_measures.bounded
import pseudo_normed_group.basic
import pseudo_normed_group.category

universe u

noncomputable theory
open_locale big_operators nnreal

section definitions

/-
structure c_measures (r : ℝ≥0) (c : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable   : ∀ s, summable (λ n, (∥ to_fun s n ∥₊ * r ^ n)))
(bdd        : ∀ s, tsum (λ n, (∥ to_fun s n ∥₊ * r ^ n)) ≤ c)
-/

structure oc_measures (r : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable'   : ∀ s, summable (λ n, ∥ to_fun s n ∥ * r ^ n))

variables {r : ℝ≥0} {S : Fintype}

instance : has_coe_to_fun (oc_measures r S) :=
⟨λ F, S → ℤ → ℤ, λ F, F.to_fun⟩

@[ext]
lemma oc_measures.ext (F G : oc_measures r S) : (F : S → ℤ → ℤ) = G → F = G :=
by { intros h, cases F, cases G, simpa }

lemma oc_measures.summable (F : oc_measures r S) (s : S) : summable (λ n, ∥ F s n ∥ * r ^ n) :=
  F.2 _

def add : oc_measures r S → oc_measures r S → oc_measures r S := λ F G,
{ to_fun := F + G,
  summable' := begin
    intros s,
    dsimp,
    have : ∀ n, ∥ F s n + G s n ∥ * r ^ n ≤ ∥ F s n ∥ * r ^ n + ∥ G s n ∥ * r ^ n,
    { intros n,
      rw ← add_mul,
      refine mul_le_mul (norm_add_le _ _) (le_refl _) _
        (add_nonneg (norm_nonneg _) (norm_nonneg _)),
      refine fpow_nonneg _ _,
      exact nnreal.coe_nonneg r },
    apply summable_of_nonneg_of_le _ this,
    { apply summable.add,
      exact F.summable s,
      exact G.summable s },
    { intros n,
      refine mul_nonneg (norm_nonneg _) _,
      refine fpow_nonneg _ _,
      exact nnreal.coe_nonneg r }
  end }

instance : has_add (oc_measures r S) := ⟨add⟩

@[simp]
lemma add_apply (F G : oc_measures r S) (s : S) (n : ℤ) : (F + G) s n = F s n + G s n := rfl

def zero : oc_measures r S :=
{ to_fun := 0,
  summable' := λ s, by simp [summable_zero] }

instance : has_zero (oc_measures r S) := ⟨zero⟩

@[simp]
lemma zero_apply (s : S) (n : ℤ) : (0 : oc_measures r S) s n = 0 := rfl

def neg : oc_measures r S → oc_measures r S := λ F,
{ to_fun := - F,
  summable' := λ s, by simp [F.summable] }

instance : has_neg (oc_measures r S) := ⟨neg⟩

@[simp]
lemma neg_apply (F : oc_measures r S) (s : S) (n : ℤ) : (-F) s n = - (F s n) := rfl

def sub : oc_measures r S → oc_measures r S → oc_measures r S := λ F G,
{ to_fun := F - G,
  summable' := sorry }

instance : has_sub (oc_measures r S) := ⟨sub⟩

@[simp]
lemma sub_apply (F G : oc_measures r S) (s : S) (n : ℤ) : (F - G) s n = F s n - G s n := rfl

instance : add_comm_group (oc_measures r S) :=
{ add_assoc := λ a b c, by { ext, simp [add_assoc] },
  zero_add := λ a, by { ext, simp },
  add_zero := λ a, by { ext, simp },
  nsmul := λ n F,
  { to_fun := nsmul n F,
    summable' := sorry },
  nsmul_zero' := λ F, by { ext, refl },
  nsmul_succ' := λ n F, by { ext, refl },
  sub_eq_add_neg := λ F G, by { ext, refl },
  gsmul := λ n F,
  { to_fun := gsmul n F,
    summable' := sorry },
  gsmul_zero' := λ F, by { ext, simpa, },
  gsmul_succ' := λ n F, by { ext, simpa, },
  gsmul_neg' := λ n F, by { ext, simpa, },
  add_left_neg := λ F, by { ext, simp },
  add_comm := λ a b, by { ext, dsimp, rw add_comm },
  ..(infer_instance : has_add _),
  ..(infer_instance : has_zero _),
  ..(infer_instance : has_neg _),
  ..(infer_instance : has_sub _) }.

instance : has_norm (oc_measures r S) :=
⟨λ F, ∑ s, ∑' n, ∥ F s n ∥ * (r : ℝ) ^ n⟩

@[simp]
lemma norm_def (F : oc_measures r S) : ∥ F ∥ = ∑ s, ∑' n, ∥ F s n ∥ * (r : ℝ)^n := rfl

/-
lemma exists_c (F : oc_measures r S) : ∃ (c : ℝ≥0),
  ∀ s : S, ∑' n, ∥ F s n ∥ * r ^ n ≤ c :=
begin
  use ∑ s, ∑' n, ∥ F s n ∥ * r ^ n,
  { apply finset.sum_nonneg,
    rintros s -,
    apply tsum_nonneg,
    intros n,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
    exact nnreal.coe_nonneg r, },
  { sorry },
end
-/

/-- This lemma puts bounds on where `F s n` can be nonzero. -/
lemma eq_zero_of_filtration (F : oc_measures r S) (c : ℝ≥0) :
  ∥ F ∥ ≤ c → ∀ (s : S) (n : ℤ), (c : ℝ) < (r : ℝ)^n → F s n = 0 :=
begin
  intros hF s n h,
  suffices : ∥ F s n ∥ < 1,
  { change abs (F s n : ℝ) < 1 at this,
    norm_cast at this,
    rwa ← int.eq_zero_iff_abs_lt_one },
  have : ∥ F s n ∥ * r ^ n ≤ ∑' k, ∥ F s k ∥ * r ^ k,
  { apply le_tsum (F.summable s),
    rintros k -,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
    exact nnreal.coe_nonneg r },
  replace this := lt_of_le_of_lt (le_trans this _) h,
  have hr₁ : 0 < (r : ℝ)^n := lt_of_le_of_lt (nnreal.coe_nonneg c) h,
  have hr₂ : (r: ℝ)^n ≠ 0 := ne_of_gt hr₁,
  convert mul_lt_mul this (le_refl ((r : ℝ) ^ n)⁻¹) _ _,
  { field_simp [hr₂] },
  { field_simp [hr₂] },
  { simp [hr₁] },
  { exact le_of_lt hr₁ },
  { refine le_trans _ hF,
    apply @finset.single_le_sum S ℝ _ (λ s, ∑' n, ∥ F s n ∥ * (r : ℝ)^n),
    { rintros s -,
      dsimp,
      apply tsum_nonneg,
      intros k,
      refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
      exact nnreal.coe_nonneg r },
    { simp } }
end

section profinite_structure

def truncate {c : ℝ≥0} (k₁ k₂ : ℤ) :
  { F : oc_measures r S | ∥ F ∥ ≤ c } → oc_measures_bdd r S k₁ k₂ c := λ F,
{ to_fun := λ s i, F s i,
  bound' := begin
    refine le_trans _ F.2,
    dsimp,
    apply finset.sum_le_sum,
    rintros s -,
    sorry,
  end }

lemma eq_iff_truncate_eq (c : ℝ≥0) (F G : {F : oc_measures r S | ∥ F ∥ ≤ c}) :
  (∀ k₁ k₂, truncate k₁ k₂ F = truncate k₁ k₂ G) → F = G :=
begin
  intros h,
  ext s i,
  specialize h i i,
  apply_fun (λ e, e s ⟨i, by simp⟩) at h,
  exact h,
end

def Icc_transition {k₁ k₂ k₁' k₂' : ℤ} (h₁ : k₁' ≤ k₁) (h₂ : k₂ ≤ k₂') :
  set.Icc k₁ k₂ → set.Icc k₁' k₂' := λ i,
⟨i, le_trans h₁ i.2.1, le_trans i.2.2 h₂⟩

def transition {c : ℝ≥0} {k₁ k₂ k₁' k₂' : ℤ} (h₁ : k₁' ≤ k₁) (h₂ : k₂ ≤ k₂') :
  oc_measures_bdd r S k₁' k₂' c → oc_measures_bdd r S k₁ k₂ c := λ F,
⟨λ s i, F s (Icc_transition h₁ h₂ i), begin
  refine le_trans _ F.2,
  apply finset.sum_le_sum,
  rintros s -,
  have : ∑ i : set.Icc k₁ k₂, ∥ F s (Icc_transition h₁ h₂ i) ∥ * (r : ℝ)^(i : ℤ) =
    ∑ i in finset.univ.image (Icc_transition h₁ h₂), ∥ F s i ∥ * (r : ℝ)^(i : ℤ),
  { rw finset.sum_image,
    { refl },
    { rintros i - j - h,
      apply subtype.ext,
      apply_fun (λ e, e.val) at h,
      exact h } },
  rw this, clear this,
  apply finset.sum_le_sum_of_subset_of_nonneg,
  { apply finset.subset_univ },
  { rintros i - -,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
    exact nnreal.coe_nonneg r }
end⟩

lemma exists_of_compat {c} (F : Π (k₁ k₂ : ℤ), oc_measures_bdd r S k₁ k₂ c)
  (compat : ∀ (k₁ k₂ k₁' k₂' : ℤ) (h₁ : k₁' ≤ k₁) (h₂ : k₂ ≤ k₂'),
    transition h₁ h₂ (F k₁' k₂') = F k₁ k₂) :
  ∃ (G : {H : oc_measures r S | ∥ H ∥ ≤ c }), ∀ k₁ k₂, truncate k₁ k₂ G = F k₁ k₂ :=
begin
  let G : oc_measures r S := ⟨λ s i, F i i s ⟨i, le_refl _, le_refl _⟩, _⟩,
  swap,
  { sorry },
  use G,
  { sorry },
  { intros k₁ k₂,
    ext s i,
    change F _ _ _ _ = _,
    have := compat i i k₁ k₂ i.2.1 i.2.2,
    apply_fun (λ e, e s ⟨i, le_refl _, le_refl _⟩) at this,
    rw ← this,
    change F k₁ k₂ _ _ = F k₁ k₂ _ _,
    congr,
    ext, refl }
end

end profinite_structure

/-
--should this be a coercion?
def c_measures_to_oc (r : ℝ≥0) (c : ℝ≥0) (S : Type*) (hS : fintype S) :
  c_measures r c S hS → oc_measures r S hS := λ f, ⟨f.to_fun, f.summable⟩

lemma oc_measures_are_c (r : ℝ≥0) (S : Type*) (hS : fintype S) (F : oc_measures r S hS) :
  ∃ (c : ℝ≥0) (f : c_measures r c S hS),
  c_measures_to_oc r c S hS f = F := sorry
-/

--needed?
instance png_oc_measures :
  profinitely_filtered_pseudo_normed_group (oc_measures r S) :=
{ filtration := λ c, { F | ∥ F ∥ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by { dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp,
  neg_mem_filtration := λ c F h, by {dsimp at *, simp [h]},
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂, begin
    dsimp at *,
    sorry,
  end,
  topology := _,
  t2 := _,
  td := _,
  compact := _,
  continuous_add' := _,
  continuous_neg' := _,
  continuous_cast_le := _ }

variable {α : Type*}

/-
def oc_functor (r : ℝ≥0) : Fintype.{u} ⥤ ProFiltPseuNormGrp.{u} :=
{ obj := λ S, ProFiltPseuNormGrp.of $ oc_measures r S,
  map := λ S T f,
  { to_fun := _,
    map_zero' := _,
    map_add' := _,
    bound' := _,
    continuous' := _ },
  map_id' := _,
  map_comp' := _ }
-/

end definitions
