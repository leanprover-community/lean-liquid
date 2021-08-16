import analysis.specific_limits
import category_theory.Fintype
import analysis.normed_space.basic

import laurent_measures.bounded
import pseudo_normed_group.basic
import pseudo_normed_group.category

universe u

noncomputable theory
open_locale big_operators nnreal classical

section definitions

/-
structure c_measures (r : ℝ≥0) (c : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable   : ∀ s, summable (λ n, (∥ to_fun s n ∥₊ * r ^ n)))
(bdd        : ∀ s, tsum (λ n, (∥ to_fun s n ∥₊ * r ^ n)) ≤ c)
-/

structure laurent_measures (r : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable'   : ∀ s, summable (λ n, ∥ to_fun s n ∥ * r ^ n))

variables {r : ℝ≥0} {S S' : Fintype.{u}}

instance : has_coe_to_fun (laurent_measures r S) :=
⟨λ F, S → ℤ → ℤ, λ F, F.to_fun⟩

@[ext]
lemma laurent_measures.ext (F G : laurent_measures r S) : (F : S → ℤ → ℤ) = G → F = G :=
by { intros h, cases F, cases G, simpa }

protected lemma laurent_measures.summable (F : laurent_measures r S) (s : S) : summable (λ n, ∥ F s n ∥ * r ^ n) :=
  F.2 _

namespace laurent_measures

-- Move me
lemma nonneg_of_norm_mul_fpow (k n : ℤ) (r : ℝ≥0) : 0 ≤ ∥ k ∥ * (r : ℝ)^n :=
mul_nonneg (norm_nonneg _) (fpow_nonneg (nnreal.coe_nonneg _) _)

def map (f : S ⟶ S') : laurent_measures r S → laurent_measures r S' := λ F,
{ to_fun := λ s' k, ∑ s in finset.univ.filter (λ t, f t = s'), F s k,
  summable' := begin
    intros s',
    have : ∀ n : ℤ, ∥ ∑ s in finset.univ.filter (λ t, f t = s'), F s n ∥ * (r : ℝ)^n ≤
      ∑ s in finset.univ.filter (λ t, f t = s'), ∥ F s n ∥ * (r : ℝ)^n := λ n,
    calc ∥ ∑ s in finset.univ.filter (λ t, f t = s'), F s n ∥ * (r : ℝ)^n ≤
      (∑ s in finset.univ.filter (λ t, f t = s'), ∥ F s n ∥) * (r : ℝ)^n :
        mul_le_mul (norm_sum_le _ _) (le_refl _) (fpow_nonneg (nnreal.coe_nonneg _) _)
        (finset.sum_nonneg $ λ s _, norm_nonneg _)
      ... = _ : by rw finset.sum_mul,
    apply summable_of_nonneg_of_le _ this,
    { apply summable_sum,
      rintros s -,
      exact F.summable s },
    { intros n,
      apply nonneg_of_norm_mul_fpow }
  end }

@[simp]
lemma map_apply (f : S ⟶ S') (F : laurent_measures r S) (s' : S') (k : ℤ) :
  map f F s' k = ∑ s in finset.univ.filter (λ t, f t = s'), F s k := rfl

@[simp]
lemma map_id : (map (𝟙 S) : laurent_measures r S → laurent_measures r S) = id :=
begin
  ext F s k,
  simp,
  change ∑ s' in finset.univ.filter (λ t, t = s), F s' k = F s k,
  simp [finset.sum_filter],
end

@[simp]
lemma map_comp {S'' : Fintype.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
  (map (f ≫ g) : laurent_measures r S → laurent_measures r S'') = map g ∘ map f :=
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

def add : laurent_measures r S → laurent_measures r S → laurent_measures r S := λ F G,
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

instance : has_add (laurent_measures r S) := ⟨add⟩

@[simp]
lemma add_apply (F G : laurent_measures r S) (s : S) (n : ℤ) : (F + G) s n = F s n + G s n := rfl

def zero : laurent_measures r S :=
{ to_fun := 0,
  summable' := λ s, by simp [summable_zero] }

instance : has_zero (laurent_measures r S) := ⟨zero⟩

@[simp]
lemma zero_apply (s : S) (n : ℤ) : (0 : laurent_measures r S) s n = 0 := rfl

def neg : laurent_measures r S → laurent_measures r S := λ F,
{ to_fun := - F,
  summable' := λ s, by simp [F.summable] }

instance : has_neg (laurent_measures r S) := ⟨neg⟩

@[simp]
lemma neg_apply (F : laurent_measures r S) (s : S) (n : ℤ) : (-F) s n = - (F s n) := rfl

def sub : laurent_measures r S → laurent_measures r S → laurent_measures r S := λ F G,
{ to_fun := F - G,
  summable' := (add F (neg G)).summable }

instance : has_sub (laurent_measures r S) := ⟨sub⟩

@[simp]
lemma sub_apply (F G : laurent_measures r S) (s : S) (n : ℤ) : (F - G) s n = F s n - G s n := rfl

example (a m : ℤ) : (-a)*m=a*(-m) := neg_mul_comm a m

instance : add_comm_monoid (laurent_measures r S) :=
{ add_assoc := λ a b c, by { ext, simp [add_assoc] },
  add_comm := λ F G, by { ext, simp [add_comm] },
  zero_add := λ a, by { ext, simp },
  add_zero := λ a, by { ext, simp },
  nsmul := λ n F,
  { to_fun := λ s k, n • (F s k),
    summable' := begin
      intro s,
      have := summable.mul_left (↑n : ℝ) (F.2 s),
      simp_rw [pi.has_mul, ← mul_assoc, int.norm_eq_abs, ← int.cast_abs] at this,
      simp_rw [int.norm_eq_abs, ← int.cast_abs, abs_nsmul, nsmul_eq_mul],
      simp only [int.cast_coe_nat, int.cast_mul, int.nat_cast_eq_coe_nat,
      int.cast_abs] at *,
      exact this,
    end },
  nsmul_zero' := λ F, by { ext, refl },
  nsmul_succ' := λ n F, by { ext, refl },
  ..(infer_instance : has_add _),
  ..(infer_instance : has_zero _) }

instance : add_comm_group (laurent_measures r S) :=
{ neg := neg,
  sub := sub,
  sub_eq_add_neg := λ F G, by { ext, refl },
  gsmul := λ n F,
  { to_fun := λ s m, gsmul n (F s m),
    summable' := begin
      intro s,
      have := summable.mul_left (↑n : ℝ) (F.2 s),
      simp only [pi.has_mul, ← mul_assoc, int.norm_eq_abs, ← int.cast_abs] at this,
      simp only [int.norm_eq_abs, ← int.cast_abs, gsmul_eq_smul, abs_gsmul],
      by_cases hn : n ≥ 0,
      { simp only [abs_of_nonneg hn, smul_eq_mul, int.cast_mul],
        exact this },
      { simp only [abs_of_neg (lt_of_not_ge hn), smul_eq_mul, int.cast_mul,
        int.cast_neg, neg_mul_eq_neg_mul_symm],
        apply summable.neg this },
    end },
  gsmul_zero' := λ F, by { ext, simpa, },
  gsmul_succ' := λ n F, by { ext, simpa [add_apply, int.coe_nat_succ, int.of_nat_eq_coe,
    gsmul_eq_smul, smul_eq_mul, add_mul, add_comm, one_mul], },
  gsmul_neg' := λ n F, by { ext, simp only [int.coe_nat_succ, int.of_nat_eq_coe,
    int.neg_succ_of_nat_coe, add_comm, gsmul_eq_smul, smul_eq_mul], ring_nf},
  add_left_neg := λ F, by { ext, simp, },
  add_comm := λ a b, by { ext, dsimp, rw add_comm },
  ..(infer_instance : add_comm_monoid _),
  ..(infer_instance : has_neg _),
  ..(infer_instance : has_sub _) }.

instance : has_norm (laurent_measures r S) :=
⟨λ F, ∑ s, ∑' n, ∥ F s n ∥ * (r : ℝ) ^ n⟩

@[simp]
lemma norm_def (F : laurent_measures r S) : ∥ F ∥ = ∑ s, ∑' n, ∥ F s n ∥ * (r : ℝ)^n := rfl

lemma map_bound (f : S ⟶ S') (F : laurent_measures r S) :
  ∥ map f F ∥ ≤ ∥ F ∥ := calc
∥ map f F ∥ = ∑ s', ∑' n, ∥ ∑ s in finset.univ.filter (λ t, f t = s'), F s n ∥ * _ : rfl
... ≤ ∑ s', ∑' n, ∑ s in finset.univ.filter (λ t, f t = s'), ∥ F s n ∥ * (r : ℝ)^n : begin
  apply finset.sum_le_sum,
  rintros s' -,
  have h1 : summable (λ n : ℤ,
    ∑ (s : S.α) in finset.univ.filter (λ (t : S.α), f t = s'), ∥F s n∥ * (r : ℝ)^n),
  { apply summable_sum,
    intros s hs,
    apply F.summable },
  have h2 : ∀ b : ℤ,
    ∥∑ (s : S.α) in finset.univ.filter (λ (t : S.α), f t = s'), F s b∥ * (r : ℝ) ^ b ≤
      ∑ (s : S.α) in finset.univ.filter (λ (t : S.α), f t = s'), ∥F s b∥ * (r : ℝ) ^ b,
  { intros b,
    rw ← finset.sum_mul,
    refine mul_le_mul _ (le_refl _) (fpow_nonneg (nnreal.coe_nonneg _) _)
      (finset.sum_nonneg $ λ _ _, norm_nonneg _),
    apply norm_sum_le },
  apply tsum_le_tsum h2 _ h1,
  { apply summable_of_nonneg_of_le _ h2,
    exact h1,
    intro b, apply nonneg_of_norm_mul_fpow }
end
... = ∑ s', ∑ s in finset.univ.filter (λ t, f t = s'), ∑' n, ∥ F s n ∥ * (r : ℝ)^n : begin
  apply finset.sum_congr rfl,
  rintros s' -,
  rw tsum_sum,
  rintros s -,
  exact F.summable _,
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

lemma norm_add (F G : laurent_measures r S) : ∥ F + G ∥ ≤ ∥ F ∥ + ∥ G ∥ :=
begin
  dsimp,
  rw ← finset.sum_add_distrib,
  apply finset.sum_le_sum,
  intros s hs,
  rw ← tsum_add (F.summable _) (G.summable _),
  apply tsum_le_tsum _ ((F + G).summable _),
  { apply summable.add (F.summable s) (G.summable s) },
  { intros b,
    dsimp,
    rw ← add_mul,
    refine mul_le_mul (norm_add_le _ _) (le_refl _) (fpow_nonneg (nnreal.coe_nonneg _) _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) }
end

/-
lemma exists_c (F : laurent_measures r S) : ∃ (c : ℝ≥0),
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
lemma eq_zero_of_filtration (F : laurent_measures r S) (c : ℝ≥0) :
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

def truncate {c : ℝ≥0} (A : finset ℤ) :
  { F : laurent_measures r S | ∥ F ∥ ≤ c } → laurent_measures_bdd r S A c := λ F,
{ to_fun := λ s i, F s i,
  bound' := begin
    refine le_trans _ F.2,
    dsimp,
    apply finset.sum_le_sum,
    rintros s -,
    let T : finset ℤ := finset.univ.image (coe : A → ℤ),
    convert sum_le_tsum A _ ((F : laurent_measures r S).summable s) using 1,
    { conv_rhs {rw ← finset.sum_attach},
      refl },
    { intros b hb,
      refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
      exact nnreal.coe_nonneg r },
  end }

lemma eq_iff_truncate_eq (c : ℝ≥0) (F G : {F : laurent_measures r S | ∥ F ∥ ≤ c}) :
  (∀ k, truncate k F = truncate k G) → F = G :=
begin
  intros h,
  ext s i,
  specialize h {i},
  apply_fun (λ e, e s ⟨i, by simp⟩) at h,
  exact h,
end


def finset_map {A B : finset ℤ} (h : B ≤ A) :
  B → A :=
λ i, ⟨i, h i.2⟩

def transition {c : ℝ≥0} {A B : finset ℤ} (h : B ≤ A) :
  laurent_measures_bdd r S A c → laurent_measures_bdd r S B c := λ F,
⟨λ s i, F s (finset_map h i), begin
  refine le_trans _ F.2,
  apply finset.sum_le_sum,
  rintros s -,
  have : ∑ i : B, ∥ F s (finset_map h i) ∥ * (r : ℝ)^(i : ℤ) =
    ∑ i in finset.univ.image (finset_map h), ∥ F s i ∥ * (r : ℝ)^(i : ℤ),
  { rw finset.sum_image,
    { refl },
    { rintros i - j - hh,
      apply subtype.ext,
      apply_fun (λ e, e.val) at hh,
      exact hh } },
  rw this, clear this,
  apply finset.sum_le_sum_of_subset_of_nonneg,
  { apply finset.subset_univ },
  { rintros i - -,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
    exact nnreal.coe_nonneg r }
end⟩

def mk_seq {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c) :
  S → ℤ → ℤ := λ s i, F {i} s ⟨i, by simp⟩

lemma mk_seq_compat {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A), transition h (F _) = F _) (s : S)
  (A : finset ℤ) (i : A) : mk_seq F s i = F A s i :=
begin
  have : ({i} : finset ℤ) ≤ A, { simp },
  specialize compat _ _ this,
  dsimp [mk_seq],
  rw ← compat,
  change (F A) s _ = _,
  congr,
  ext,
  refl,
end

lemma mk_seq_compat_summable {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A), transition h (F _) = F _) (s : S) :
  summable (λ k : ℤ, ∥ mk_seq F s k ∥ * (r : ℝ)^k) :=
begin
  apply summable_of_sum_le,
  { intro k,
    dsimp,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg (nnreal.coe_nonneg _) _) },
  { intros A,
    rw ← finset.sum_attach,
    refine le_trans _ (F A).bound,
    simp_rw mk_seq_compat _ compat,
    dsimp,
    apply @finset.single_le_sum S ℝ _ (λ s, ∑ (i : A), ∥ F A s i ∥ * (r : ℝ)^(i : ℤ)),
    swap, { simp },
    rintro s -,
    apply finset.sum_nonneg,
    rintros a -,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg (nnreal.coe_nonneg _) _) },
end

lemma mk_seq_compat_sum_le {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A), transition h (F _) = F _)  :
  ∑ (s : S), ∑' (k : ℤ), ∥ mk_seq F s k ∥ * (r : ℝ)^k ≤ c :=
begin
  rw ← tsum_sum,
  swap, { intros s hs, apply mk_seq_compat_summable _ compat },
  have : ∀ A : finset ℤ,
    ∑ (b : A), ∑ (s : S), ∥ F A s b ∥ * (r : ℝ)^(b : ℤ) ≤ c,
  { intros A,
    rw finset.sum_comm,
    exact (F A).bound },
  apply tsum_le_of_sum_le,
  { apply summable_sum,
    intros s hs,
    apply mk_seq_compat_summable _ compat },
  intros I,
  rw finset.sum_comm,
  convert (F I).bound using 1,
  dsimp,
  apply finset.sum_congr rfl,
  rintros s -,
  rw ← finset.sum_attach,
  apply finset.sum_congr rfl,
  rintros i -,
  simp_rw [mk_seq_compat _ compat],
end

lemma exists_of_compat {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A),
    transition h (F _) = F _) :
  ∃ (G : {H : laurent_measures r S | ∥ H ∥ ≤ c }), ∀ (k : finset ℤ), truncate k G = F k :=
begin
  let G : laurent_measures r S := ⟨mk_seq F, mk_seq_compat_summable _ compat⟩,
  use G,
  { apply mk_seq_compat_sum_le _ compat },
  { intros k,
    ext s i,
    change F _ _ _ = _,
    have := compat k {i} (by simp),
    apply_fun (λ e, e s ⟨i, by simp⟩) at this,
    erw ← this,
    change F k _ _ = F k _ _,
    congr,
    ext, refl }
end

variables (r S)
open category_theory
def laurent_measures_bdd_functor (c : ℝ≥0) [fact (0 < r)] :
  (as_small (finset ℤ))ᵒᵖ ⥤ Fintype :=
{ obj := λ A, Fintype.of $ laurent_measures_bdd r S (ulift.down A.unop) c,
  map := λ A B f, transition (le_of_hom $ ulift.down f.unop) }.

def laurent_measures_bdd_equiv (c : ℝ≥0) [fact (0 < r)] : { F : laurent_measures r S | ∥ F ∥ ≤ c } ≃
  (Profinite.limit_cone (laurent_measures_bdd_functor r S c ⋙ Fintype.to_Profinite)).X :=
equiv.of_bijective (λ F, ⟨λ A, truncate (ulift.down A.unop) F, begin
  intros A B f,
  ext,
  refl,
end⟩)
begin
  split,
  { intros F G h,
    apply eq_iff_truncate_eq,
    intros k,
    dsimp at h,
    apply_fun (λ e, e.1 (opposite.op ⟨k⟩)) at h,
    exact h },
  { rintros ⟨F, hF⟩,
    dsimp at F hF,
    obtain ⟨G,hG⟩ := exists_of_compat (λ A, F (opposite.op ⟨A⟩)) _,
    { use G,
      ext : 2,
      dsimp,
      have := hG (ulift.down x.unop),
      convert this,
      rw ← x.op_unop,
      congr' 1,
      ext,
      refl },
    { intros A B h,
      let e : (opposite.op $ as_small.up.obj A) ⟶ (opposite.op $ as_small.up.obj B) :=
        quiver.hom.op (as_small.up.map (hom_of_le h)),
      exact hF e } }
end

instance (c : ℝ≥0) [fact (0 < r)] : topological_space {F : laurent_measures r S | ∥ F ∥ ≤ c} :=
topological_space.induced (laurent_measures_bdd_equiv r S c) infer_instance

def laurent_measures_bdd_homeo (c : ℝ≥0) [fact (0 < r)] : { F : laurent_measures r S | ∥ F ∥ ≤ c } ≃ₜ
  (Profinite.limit_cone (laurent_measures_bdd_functor r S c ⋙ Fintype.to_Profinite)).X :=
{ continuous_to_fun := continuous_induced_dom,
  continuous_inv_fun := begin
    have : inducing (laurent_measures_bdd_equiv r S c) := ⟨rfl⟩,
    rw this.continuous_iff,
    dsimp,
    convert continuous_id,
    ext,
    simp,
  end,
  ..(laurent_measures_bdd_equiv _ _ _) }

instance (c : ℝ≥0) [fact (0 < r)] : t2_space { F : laurent_measures r S | ∥ F ∥ ≤ c } :=
⟨λ x y h, separated_by_continuous (laurent_measures_bdd_homeo r S c).continuous
(λ cc, h $ by simpa using congr_arg (laurent_measures_bdd_homeo r S c).symm cc)⟩

instance (c : ℝ≥0) [fact (0 < r)] : totally_disconnected_space
  { F : laurent_measures r S | ∥ F ∥ ≤ c } :=
begin
  constructor,
  rintros A - hA,
  suffices : ((laurent_measures_bdd_homeo r S c) '' A).subsingleton,
  { intros x hx y hy,
    apply_rules [(laurent_measures_bdd_homeo r S c).injective, this, set.mem_image_of_mem] },
  obtain ⟨h⟩ := (infer_instance : totally_disconnected_space
   (Profinite.limit_cone (laurent_measures_bdd_functor r S c ⋙ Fintype.to_Profinite)).X),
  refine h _ (by tauto) (is_preconnected.image hA _ _),
  exact (laurent_measures_bdd_homeo r S c).continuous.continuous_on,
end

instance (c : ℝ≥0) [fact (0 < r)] : compact_space {F : laurent_measures r S | ∥ F ∥ ≤ c} :=
begin
  constructor,
  rw (laurent_measures_bdd_homeo r S c).embedding.is_compact_iff_is_compact_image,
  simp [compact_univ],
end

@[continuity]
lemma truncate_continuous (c : ℝ≥0) [fact (0 < r)] (A : finset ℤ) :
  continuous (truncate A : _ → laurent_measures_bdd r S _ c) :=
begin
  let g₁ :=
    (Profinite.limit_cone (laurent_measures_bdd_functor.{u} r S c ⋙ Fintype.to_Profinite)).π.app
    (opposite.op $ ulift.up A),
  let g₂ := (laurent_measures_bdd_homeo r S c),
  change continuous (g₁ ∘ g₂),
  continuity,
end

lemma continuous_iff (c : ℝ≥0) [fact (0 < r)] {α : Type*} [topological_space α]
  (f : α → { F : laurent_measures r S | ∥ F ∥ ≤ c }) :
  continuous f ↔ ∀ (A : finset ℤ), continuous ((truncate A) ∘ f) :=
begin
  split,
  { intros hf A, continuity },
  { intros h,
    rw ← (laurent_measures_bdd_homeo r S c).comp_continuous_iff,
    apply continuous_subtype_mk,
    apply continuous_pi,
    intros A,
    apply h }
end

end profinite_structure

/-
--should this be a coercion?
def c_measures_to_oc (r : ℝ≥0) (c : ℝ≥0) (S : Type*) (hS : fintype S) :
  c_measures r c S hS → laurent_measures r S hS := λ f, ⟨f.to_fun, f.summable⟩

lemma laurent_measures_are_c (r : ℝ≥0) (S : Type*) (hS : fintype S) (F : laurent_measures r S hS) :
  ∃ (c : ℝ≥0) (f : c_measures r c S hS),
  c_measures_to_oc r c S hS f = F := sorry
-/

--needed?
instance pnf_laurent_measures : pseudo_normed_group (laurent_measures r S) :=
{ filtration := λ c, { F | ∥ F ∥ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by {dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp,
  neg_mem_filtration := λ c F h, by {dsimp at *, simp [h]},
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂, begin
    refine le_trans (norm_add _ _) _,
    rw nnreal.coe_add,
    exact add_le_add h₁ h₂,
  end }

instance pfpng_laurent_measures [fact (0 < r)] :
  profinitely_filtered_pseudo_normed_group (laurent_measures r S) :=
{ continuous_add' := begin
    intros c₁ c₂,
    rw continuous_iff,
    intros A,
    let E : laurent_measures_bdd r S A c₁ × laurent_measures_bdd r S A c₂ →
      laurent_measures_bdd r S A (c₁ + c₂) := λ G, ⟨G.1 + G.2, _⟩,
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
      (truncate A : _ → laurent_measures_bdd r S A (c₁ + c₂)) ∘ pseudo_normed_group.add' =
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
    let E : laurent_measures_bdd r S A c → laurent_measures_bdd r S A c :=
      λ G, ⟨- G, _⟩,
    swap, {
      convert G.2 using 1,
      apply finset.sum_congr rfl,
      intros s hs,
      apply finset.sum_congr rfl,
      intros x hx,
      congr' 1,
      simpa },
    have : (truncate A : _ → laurent_measures_bdd r S A c) ∘ pseudo_normed_group.neg' =
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
    let g : laurent_measures_bdd r S A c₁ → laurent_measures_bdd r S A c₂ :=
      λ g, ⟨g, le_trans g.2 h.out⟩,
    have : (truncate A : _ → laurent_measures_bdd r S A c₂) ∘ pseudo_normed_group.cast_le =
      g ∘ truncate A,
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply truncate_continuous }
  end,
  ..(infer_instance : (pseudo_normed_group (laurent_measures r S))) }

variable {α : Type*}

open pseudo_normed_group profinitely_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group

def map_hom [fact (0 < r)] (f : S ⟶ S') :
  comphaus_filtered_pseudo_normed_group_hom (laurent_measures r S) (laurent_measures r S') :=
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
    let e : filtration (laurent_measures r S') c₂ → filtration (laurent_measures r S') (c₁ ⊔ c₂) :=
      cast_le,
    suffices : continuous (e ∘ f₀),
    { rwa (embedding_cast_le _ _).to_inducing.continuous_iff },
    rw continuous_iff,
    intros T,
    let e' : laurent_measures_bdd r S T c₁ → laurent_measures_bdd r S T (c₁ ⊔ c₂) :=
      λ F, ⟨F, le_trans F.bound $ by exact_mod_cast le_sup_left⟩,
    have : truncate T ∘ e ∘ f₀ = laurent_measures_bdd.map f ∘ e' ∘ truncate T,
    { ext F s' t,
      change (f₀ F : laurent_measures r S') s' t = _,
      rw ← h,
      refl },
    rw this,
    continuity,
  end }

@[simps]
def functor (r : ℝ≥0) [fact (0 < r)] : Fintype.{u} ⥤ ProFiltPseuNormGrp.{u} :=
{ obj := λ S, ProFiltPseuNormGrp.of $ laurent_measures r S,
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
  end }

end laurent_measures

end definitions
