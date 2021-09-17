import analysis.specific_limits
import category_theory.Fintype
import analysis.normed_space.basic

import pseudo_normed_group.basic
import pseudo_normed_group.category

import for_mathlib.nnreal

universe u

noncomputable theory
open_locale big_operators nnreal classical

section definitions

structure real_measures (p : ℝ≥0) (S : Fintype) :=
(to_fun    : S → ℤ → ℝ)
(summable' : ∀ s, summable (λ n, ∥to_fun s n∥₊ * p ^ n))

variables {p : ℝ≥0} {S S' : Fintype.{u}}

notation `ℳ` := real_measures

instance : has_coe_to_fun (ℳ p S) :=
⟨λ F, S → ℤ → ℝ, λ F, F.to_fun⟩

@[ext]
lemma real_measures.ext (F G : ℳ p S) : (F : S → ℤ → ℝ) = G → F = G :=
by { intros h, cases F, cases G, simpa }

protected lemma real_measures.summable_nnreal (F : ℳ p S) (s : S) :
  summable (λ n, ∥F s n∥₊ * p ^ n) :=
F.2 _

protected lemma real_measures.summable (F : ℳ p S) (s : S) : summable (λ n, ∥F s n∥ * p ^ n) :=
by simpa only [← nnreal.summable_coe, coe_nnnorm, nnreal.coe_mul, nnreal.coe_fpow]
  using F.summable_nnreal s

namespace real_measures

-- Move me
lemma nonneg_of_norm_mul_fpow (k n : ℤ) (p : ℝ≥0) : 0 ≤ ∥ k ∥ * (p : ℝ)^n :=
mul_nonneg (norm_nonneg _) (fpow_nonneg (nnreal.coe_nonneg _) _)

def map (f : S ⟶ S') : ℳ p S → ℳ p S' := λ F,
{ to_fun := λ s' k, ∑ s in finset.univ.filter (λ t, f t = s'), F s k,
  summable' := begin
    intros s',
    have : ∀ n : ℤ, ∥∑ s in finset.univ.filter (λ t, f t = s'), F s n∥₊ * p^n ≤
      ∑ s in finset.univ.filter (λ t, f t = s'), ∥F s n∥₊ * p^n := λ n,
    calc ∥∑ s in finset.univ.filter (λ t, f t = s'), F s n∥₊ * p^n ≤
      (∑ s in finset.univ.filter (λ t, f t = s'), ∥F s n∥₊) * p^n :
        mul_le_mul' (nnnorm_sum_le _ _) (le_refl _)
      ... = _ : by rw finset.sum_mul,
    apply nnreal.summable_of_le this,
    { apply summable_sum,
      rintros s -,
      exact F.summable_nnreal s },
  end }

@[simp]
lemma map_apply (f : S ⟶ S') (F : ℳ p S) (s' : S') (k : ℤ) :
  map f F s' k = ∑ s in finset.univ.filter (λ t, f t = s'), F s k := rfl

@[simp]
lemma map_id : (map (𝟙 S) : ℳ p S → ℳ p S) = id :=
begin
  ext F s k,
  simp,
  change ∑ s' in finset.univ.filter (λ t, t = s), F s' k = F s k,
  simp [finset.sum_filter],
end

@[simp]
lemma map_comp {S'' : Fintype.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
  (map (f ≫ g) : ℳ p S → ℳ p S'') = map g ∘ map f :=
begin
  ext F s k,
  simp only [function.comp_app, map_apply, finset.sum_congr],
  rw ← finset.sum_bUnion,
  { apply finset.sum_congr,
    { change finset.univ.filter (λ t, g (f t) = s) = _,
      ext i,
      split,
      { intro hi, simpa using hi },
      { intro hi, simpa using hi } },
    { tauto } },
  { intros i hi j hj h k hk,
    simp at hi hj hk,
    refine h _,
    rw [← hk.1, ← hk.2] }
end

def add : ℳ p S → ℳ p S → ℳ p S := λ F G,
{ to_fun := F + G,
  summable' := begin
    intros s,
    dsimp,
    have : ∀ n, ∥F s n + G s n∥₊ * p ^ n ≤ ∥F s n∥₊ * p ^ n + ∥G s n∥₊ * p ^ n,
    { intros n,
      rw ← add_mul,
      exact mul_le_mul' (norm_add_le _ _) (le_refl _) },
    apply nnreal.summable_of_le this,
    { apply summable.add,
      exact F.summable_nnreal s,
      exact G.summable_nnreal s },
  end }

instance : has_add (ℳ p S) := ⟨add⟩

@[simp]
lemma add_apply (F G : ℳ p S) (s : S) (n : ℤ) : (F + G) s n = F s n + G s n := rfl

def zero : ℳ p S :=
{ to_fun := 0,
  summable' := λ s, by simp [summable_zero] }

instance : has_zero (ℳ p S) := ⟨zero⟩

@[simp]
lemma zero_apply (s : S) (n : ℤ) : (0 : ℳ p S) s n = 0 := rfl

def neg : ℳ p S → ℳ p S := λ F,
{ to_fun := - F,
  summable' := λ s, by simp [F.summable_nnreal] }

instance : has_neg (ℳ p S) := ⟨neg⟩

@[simp]
lemma neg_apply (F : ℳ p S) (s : S) (n : ℤ) : (-F) s n = - (F s n) := rfl

def sub : ℳ p S → ℳ p S → ℳ p S := λ F G,
{ to_fun := F - G,
  summable' := (add F (neg G)).summable_nnreal }

instance : has_sub (ℳ p S) := ⟨sub⟩

@[simp]
lemma sub_apply (F G : ℳ p S) (s : S) (n : ℤ) : (F - G) s n = F s n - G s n := rfl

example (a m : ℤ) : (-a)*m=a*(-m) := neg_mul_comm a m

instance : add_comm_monoid (ℳ p S) :=
{ add_assoc := λ a b c, by { ext, simp only [add_assoc, add_apply] },
  add_comm := λ F G, by { ext, simp only [add_comm, add_apply] },
  zero_add := λ a, by { ext, simp only [add_apply, zero_apply, zero_add] },
  add_zero := λ a, by { ext, simp only [add_apply, zero_apply, add_zero] },
  nsmul := λ n F,
  { to_fun := λ s k, n • (F s k),
    summable' := begin
      intro s,
      simpa only [real.nnnorm_coe_nat, nsmul_eq_mul, normed_field.nnnorm_mul, mul_assoc]
        using summable.mul_left (↑n : ℝ≥0) (F.summable_nnreal s),
    end },
  nsmul_zero' := λ F, by { ext, refl },
  nsmul_succ' := λ n F, by { ext, refl },
  ..(infer_instance : has_add _),
  ..(infer_instance : has_zero _) }

instance : add_comm_group (ℳ p S) :=
{ neg := neg,
  sub := sub,
  sub_eq_add_neg := λ F G, by { ext, refl },
  gsmul := λ n F,
  { to_fun := λ s m, n • (F s m),
    summable' := begin
      intro s,
      have := summable.mul_left (n.nat_abs : ℝ≥0) (F.summable_nnreal s),
      convert this using 1,
      simp only [mul_assoc, gsmul_eq_mul, normed_field.nnnorm_mul, nnreal.coe_nat_abs],
      -- need a lemma that converts ∥↑n∥₊ to ∥n∥₊
      sorry
    end },
  gsmul_zero' := λ F, by { ext, simp only [zero_smul, zero_apply], refl },
  gsmul_succ' := λ n F, by { ext, simp only [add_apply, int.coe_nat_succ, int.of_nat_eq_coe,
    gsmul_eq_smul, smul_eq_mul, add_mul, add_comm, one_mul, add_smul, one_smul], refl },
  gsmul_neg' := λ n F, by { ext, simp only [int.coe_nat_succ, int.of_nat_eq_coe,
    int.neg_succ_of_nat_coe, add_comm, gsmul_eq_smul, smul_eq_mul, neg_smul], refl },
  add_left_neg := λ F, by { ext, simp only [add_apply, add_left_neg, neg_apply, zero_apply], },
  add_comm := λ a b, by { ext, dsimp, rw add_comm },
  ..(infer_instance : add_comm_monoid _),
  ..(infer_instance : has_neg _),
  ..(infer_instance : has_sub _) }.

instance : has_norm (ℳ p S) :=
⟨λ F, ∑ s, ∑' n, ∥ F s n ∥ * (p : ℝ) ^ n⟩

lemma norm_def (F : ℳ p S) : ∥F∥ = ∑ s, ∑' n, ∥F s n∥ * (p : ℝ)^n := rfl

instance : has_nnnorm (ℳ p S) :=
⟨λ F, ∑ s, ∑' n, ∥F s n∥₊ * p ^ n⟩

lemma nnnorm_def (F : ℳ p S) : ∥F∥₊ = ∑ s, ∑' n, ∥F s n∥₊ * p^n := rfl

@[simp] protected lemma coe_nnnorm (F : ℳ p S) : (∥F∥₊ : ℝ) = ∥F∥ :=
by simp only [norm_def, nnnorm_def, nnreal.coe_sum, nnreal.coe_tsum,
  nnreal.coe_mul, nnreal.coe_fpow, coe_nnnorm]

lemma map_bound (f : S ⟶ S') (F : ℳ p S) :
  ∥map f F∥₊ ≤ ∥F∥₊ :=
calc ∥map f F∥₊
    = ∑ s', ∑' n, ∥∑ s in finset.univ.filter (λ t, f t = s'), F s n∥₊ * _ : rfl
... ≤ ∑ s', ∑' n, ∑ s in finset.univ.filter (λ t, f t = s'), ∥F s n∥₊ * p^n : begin
  apply finset.sum_le_sum,
  rintros s' -,
  have h1 : summable (λ n : ℤ,
    ∑ (s : S.α) in finset.univ.filter (λ (t : S.α), f t = s'), ∥F s n∥₊ * p^n),
  { apply summable_sum,
    intros s hs,
    apply F.summable_nnreal },
  have h2 : ∀ b : ℤ,
    ∥∑ (s : S.α) in finset.univ.filter (λ (t : S.α), f t = s'), F s b∥₊ * p ^ b ≤
      ∑ (s : S.α) in finset.univ.filter (λ (t : S.α), f t = s'), ∥F s b∥₊ * p ^ b,
  { intros b,
    rw ← finset.sum_mul,
    refine mul_le_mul' _ (le_refl _),
    apply nnnorm_sum_le },
  exact tsum_le_tsum h2 (nnreal.summable_of_le h2 h1) h1,
end
... = ∑ s', ∑ s in finset.univ.filter (λ t, f t = s'), ∑' n, ∥F s n∥₊ * p^n : begin
  apply finset.sum_congr rfl,
  rintros s' -,
  rw tsum_sum,
  rintros s -,
  exact F.summable_nnreal _,
end
... = _ : begin
  dsimp,
  rw ← finset.sum_bUnion,
  apply finset.sum_congr,
  { ext s,
    split,
    { intro h, simp },
    { intro h, simp } },
  { tauto },
  { rintro x - y - h i hi,
    apply h,
    simp at hi,
    rw [← hi.1, ← hi.2] }
end

lemma nnnorm_add (F G : ℳ p S) : ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  dsimp [nnnorm_def],
  rw ← finset.sum_add_distrib,
  apply finset.sum_le_sum,
  intros s hs,
  rw ← tsum_add (F.summable_nnreal _) (G.summable_nnreal _),
  apply tsum_le_tsum _ ((F + G).summable_nnreal _),
  { apply summable.add (F.summable_nnreal s) (G.summable_nnreal s) },
  { intros b,
    dsimp,
    rw ← add_mul,
    refine mul_le_mul' (norm_add_le _ _) (le_refl _) }
end

--needed?
instance png_real_measures : pseudo_normed_group (ℳ p S) :=
{ filtration := λ c, { F | ∥F∥₊ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by {dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp only [nnnorm_def, nnnorm_zero, tsum_zero, zero_mul, zero_le',
    finset.sum_const_zero, set.mem_set_of_eq, zero_apply],
  neg_mem_filtration := λ c F h, by { dsimp [nnnorm_def] at *, simp only [h, nnnorm_neg] },
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂, (nnnorm_add _ _).trans (add_le_add h₁ h₂) }

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
