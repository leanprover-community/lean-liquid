import analysis.special_functions.pow
import analysis.specific_limits
import category_theory.Fintype
import analysis.normed_space.basic

import pseudo_normed_group.basic
import pseudo_normed_group.category

import for_mathlib.nnreal
import for_mathlib.real

universe u

noncomputable theory
open_locale big_operators nnreal classical

section definitions

@[nolint unused_arguments, derive add_comm_group]
def real_measures (p : ℝ≥0) (S : Fintype) := S → ℝ

variables {p : ℝ≥0} {S S' : Fintype.{u}}

notation `ℳ` := real_measures

namespace real_measures

-- Move me
lemma nonneg_of_norm_mul_fpow (k n : ℤ) (p : ℝ≥0) : 0 ≤ ∥ k ∥ * (p : ℝ)^n :=
mul_nonneg (norm_nonneg _) (fpow_nonneg (nnreal.coe_nonneg _) _)

def map (f : S ⟶ S') : ℳ p S → ℳ p S' :=
λ F s', ∑ s in finset.univ.filter (λ t, f t = s'), F s

@[simp]
lemma map_apply (f : S ⟶ S') (F : ℳ p S) (s' : S') :
  map f F s' = ∑ s in finset.univ.filter (λ t, f t = s'), F s := rfl

@[simp]
lemma map_id : (map (𝟙 S) : ℳ p S → ℳ p S) = id :=
begin
  ext F s,
  rw [map_apply, finset.sum_filter, id.def],
  simp only [Fintype.id_apply, finset.sum_ite_eq', finset.mem_univ, if_true],
end

@[simp]
lemma map_comp {S'' : Fintype.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
  (map (f ≫ g) : ℳ p S → ℳ p S'') = map g ∘ map f :=
begin
  ext F s,
  simp only [function.comp_app, map_apply],
  convert finset.sum_bUnion _ using 1, swap 2, { classical, apply_instance },
  { apply finset.sum_congr,
    { change finset.univ.filter (λ t, g (f t) = s) = _,
      ext i,
      simp only [true_and, exists_prop, finset.mem_univ, finset.mem_bUnion,
        exists_eq_right', finset.mem_filter] },
    { intros, refl } },
  { intros i hi j hj h k hk,
    refine h _,
    simp only [true_and, finset.inf_eq_inter, finset.mem_univ,
      finset.mem_filter, finset.mem_inter] at hk,
    rw [← hk.1, ← hk.2] }
end

@[simp] lemma zero_apply (s : S) : (0 : ℳ p S) s = 0 := rfl

@[simp] lemma add_apply (F G : ℳ p S) (s : S) : (F + G) s = F s + G s := rfl

@[simp] lemma neg_apply (F : ℳ p S) (s : S) : (-F) s = - (F s) := rfl

@[simp] lemma sub_apply (F G : ℳ p S) (s : S) : (F - G) s = F s - G s := rfl

instance : has_norm (ℳ p S) := ⟨λ F, ∑ s, ∥F s∥ ^ (p:ℝ)⟩

lemma norm_def (F : ℳ p S) : ∥F∥ = ∑ s, ∥F s∥ ^ (p:ℝ) := rfl

instance : has_nnnorm (ℳ p S) := ⟨λ F, ∑ s, ∥F s∥₊ ^ (p:ℝ)⟩

lemma nnnorm_def (F : ℳ p S) : ∥F∥₊ = ∑ s, ∥F s∥₊ ^ (p:ℝ) := rfl

@[simp] protected lemma coe_nnnorm (F : ℳ p S) : (∥F∥₊ : ℝ) = ∥F∥ :=
by simp only [norm_def, nnnorm_def, nnreal.coe_sum, nnreal.coe_rpow, coe_nnnorm]

lemma map_bound [hp : fact (p ≤ 1)] (f : S ⟶ S') (F : ℳ p S) :
  ∥map f F∥₊ ≤ ∥F∥₊ :=
begin
  calc ∑ s', ∥∑ s in finset.univ.filter (λ t, f t = s'), F s∥₊ ^ (p:ℝ)
      ≤  ∑ s' : S', ∑ s in finset.univ.filter (λ t, f t = s'), ∥F s∥₊ ^ (p:ℝ) : _
  ... = ∑ s, ∥F s∥₊ ^ (p:ℝ) : _,
  { apply finset.sum_le_sum,
    rintros s' -, sorry, },
  { rw ← finset.sum_bUnion,
    { refine finset.sum_congr _ _,
      { ext s,
        simp only [true_and, finset.mem_univ, finset.mem_bUnion, iff_true,
          exists_true_left, finset.mem_filter],
        refine ⟨_, finset.mem_univ _, rfl⟩, },
      { intros, refl } },
    { rintro x - y - h i hi,
      apply h,
      simp only [true_and, finset.inf_eq_inter, finset.mem_univ,
        finset.mem_filter, finset.mem_inter] at hi,
      rw [← hi.1, ← hi.2] } },

end

@[simp] protected lemma nnnorm_zero [hp : fact (0 < p)] : ∥(0 : ℳ p S)∥₊ = 0 :=
begin
  rw [nnnorm_def, finset.sum_eq_zero],
  rintro s -,
  rw [zero_apply, nnnorm_zero, nnreal.zero_rpow],
  exact_mod_cast hp.out.ne',
end

protected lemma nnnorm_add (F G : ℳ p S) : ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  dsimp [nnnorm_def],
  rw ← finset.sum_add_distrib,
  apply finset.sum_le_sum,
  intros s hs,
  sorry
end

--needed?
instance png_real_measures [fact (0 < p)] : pseudo_normed_group (ℳ p S) :=
{ filtration := λ c, { F | ∥F∥₊ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by {dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp only [real_measures.nnnorm_zero, zero_le', set.mem_set_of_eq],
  neg_mem_filtration := λ c F h, by { dsimp [nnnorm_def] at *, simp only [h, nnnorm_neg] },
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂,
    (real_measures.nnnorm_add _ _).trans (add_le_add h₁ h₂) }

/-

instance pfpng_real_measures [fact (0 < p)] :
  comphaus_filtered_pseudo_normed_group (ℳ p S) :=
{ continuous_add' := begin
    intros c₁ c₂,
    rw continuous_iff,
    intros A,
    let E : real_measures_bdd p S A c₁ × real_measures_bdd p S A c₂ →
      real_measures_bdd p S A (c₁ + c₂) := λ G, ⟨G.1 + G.2, _⟩,
    swap, {
      rw nnreal.coe_add,
      refine le_trans _ (add_le_add G.fst.2 G.snd.2),
      rw ← finset.sum_add_distrib,
      apply finset.sum_le_sum,
      intros i hi,
      rw ← finset.sum_add_distrib,
      apply finset.sum_le_sum,
      intros j hj,
      rw ← add_mul,
      refine mul_le_mul (norm_add_le _ _) (le_refl _)
        (fpow_nonneg (nnreal.coe_nonneg _) _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) },
    have :
      (truncate A : _ → real_measures_bdd p S A (c₁ + c₂)) ∘ pseudo_normed_group.add' =
      E ∘ (prod.map (truncate A) (truncate A)),
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply continuous.prod_map,
      all_goals {apply truncate_continuous} }
  end,
  continuous_neg' := begin
    intros c,
    rw continuous_iff,
    intros A,
    let E : real_measures_bdd p S A c → real_measures_bdd p S A c :=
      λ G, ⟨- G, _⟩,
    swap, {
      convert G.2 using 1,
      apply finset.sum_congr rfl,
      intros s hs,
      apply finset.sum_congr rfl,
      intros x hx,
      congr' 1,
      simpa },
    have : (truncate A : _ → real_measures_bdd p S A c) ∘ pseudo_normed_group.neg' =
      E ∘ truncate A,
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply truncate_continuous }
  end,
  continuous_cast_le := begin
    introsI c₁ c₂ h,
    rw continuous_iff,
    intros A,
    let g : real_measures_bdd p S A c₁ → real_measures_bdd p S A c₂ :=
      λ g, ⟨g, le_trans g.2 h.out⟩,
    have : (truncate A : _ → real_measures_bdd p S A c₂) ∘ pseudo_normed_group.cast_le =
      g ∘ truncate A,
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply truncate_continuous }
  end,
  ..(infer_instance : (pseudo_normed_group (ℳ p S))) }

variable {α : Type*}

open pseudo_normed_group profinitely_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group

def map_hom [fact (0 < p)] (f : S ⟶ S') :
  comphaus_filtered_pseudo_normed_group_hom (ℳ p S) (ℳ p S') :=
{ to_fun := map f,
  map_zero' := begin
    ext F s i,
    simp,
  end,
  map_add' := begin
    intros F G,
    ext s i,
    simp [← finset.sum_bUnion, ← finset.sum_add_distrib],
  end,
  bound' := begin
    -- should we introduce strict morphisms, and the strict category, so we can have limits?
    use 1,
    rintros c F (hF : ∥ F ∥ ≤ c),
    exact le_trans (map_bound _ _) (by simpa),
  end,
  continuous' := begin
    intros c₁ c₂ f₀ h,
    haveI h₂ : fact (c₂ ≤ c₁ ⊔ c₂) := ⟨le_sup_right⟩,
    let e : filtration (ℳ p S') c₂ → filtration (ℳ p S') (c₁ ⊔ c₂) :=
      cast_le,
    suffices : continuous (e ∘ f₀),
    { rwa (embedding_cast_le _ _).to_inducing.continuous_iff },
    rw continuous_iff,
    intros T,
    let e' : real_measures_bdd p S T c₁ → real_measures_bdd p S T (c₁ ⊔ c₂) :=
      λ F, ⟨F, le_trans F.bound $ by exact_mod_cast le_sup_left⟩,
    have : truncate T ∘ e ∘ f₀ = real_measures_bdd.map f ∘ e' ∘ truncate T,
    { ext F s' t,
      change (f₀ F : ℳ p S') s' t = _,
      rw ← h,
      refl },
    rw this,
    continuity,
  end }

@[simps]
def functor (p : ℝ≥0) [fact (0 < p)] : Fintype.{u} ⥤ CompHausFiltPseuNormGrp.{u} :=
{ obj := λ S, CompHausFiltPseuNormGrp.of $ ℳ p S,
  map := λ S T f, map_hom f,
  map_id' := begin
    intros S,
    ext1,
    dsimp [map_hom],
    simp,
  end,
  map_comp' := begin
    intros S S' S'' f g,
    ext1,
    dsimp [map_hom],
    simp,
  end}

-/

end real_measures

end definitions
