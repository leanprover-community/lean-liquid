import data.fintype.card

import facts
import hacks_and_tricks.type_pow

import Mbar.basic
import pseudo_normed_group.profinitely_filtered

/-!
# $\overline{\mathcal{M}}_{r'}(S)_{≤ c}$

In this file we put a profinite topology on the subspace
`Mbar_le r' S c` of `Mbar r' S` consisting of power series
`F_s = ∑ a_{n,s}T^n ∈ Tℤ⟦T⟧` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c`.
-/

universe u

noncomputable theory
open_locale big_operators nnreal
open pseudo_normed_group
local attribute [instance] type_pow

variables {r' : ℝ≥0} {S : Type u} [fintype S] {c c₁ c₂ c₃ : ℝ≥0}

/-- `Mbar_le r' S c` is the set of power series
`F_s = ∑ a_{n,s}T^n ∈ Tℤ[[T]]` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c` -/
def Mbar_le (r' : ℝ≥0) (S : Type u) [fintype S] (c : ℝ≥0) :=
{ F : Mbar r' S // F ∈ filtration (Mbar r' S) c }

namespace Mbar_le

instance has_coe : has_coe (Mbar_le r' S c) (Mbar r' S) := ⟨subtype.val⟩

instance has_coe_to_fun : has_coe_to_fun (Mbar_le r' S c) := ⟨λ F, S → ℕ → ℤ, λ F, F.1⟩

@[simp] lemma coe_coe_to_fun (F : Mbar_le r' S c) : ⇑(F : Mbar r' S) = F := rfl

@[simp] lemma coe_mk (x h) : ((⟨x, h⟩ : Mbar_le r' S c) : S → ℕ → ℤ) = x := rfl

@[simp] protected lemma coeff_zero (x : Mbar_le r' S c) (s : S) : x s 0 = 0 := x.1.coeff_zero' s

protected lemma summable (x : Mbar_le r' S c) (s : S) :
  summable (λ n, (↑(x s n).nat_abs * r'^n)) := x.1.summable' s

protected lemma mem_filtration (x : Mbar_le r' S c) :
  x.1 ∈ filtration (Mbar r' S) c := x.property

/-- The inclusion map `Mbar_le r' S c₁ → Mbar_le r' S c₂` for `c₁ ≤ c₂`. -/
protected def cast_le [hc : fact (c₁ ≤ c₂)] (x : Mbar_le r' S c₁) : Mbar_le r' S c₂ :=
⟨⟨x, x.coeff_zero, x.summable⟩, filtration_mono hc.out x.mem_filtration⟩

@[simp] lemma coe_cast_le [hc : fact (c₁ ≤ c₂)] (x : Mbar_le r' S c₁) :
  ((x.cast_le : Mbar_le r' S c₂) : Mbar r' S) = x :=
by { ext, refl }

@[simp] lemma cast_le_apply [hc : fact (c₁ ≤ c₂)] (x : Mbar_le r' S c₁) (s : S) (i : ℕ) :
  (x.cast_le : Mbar_le r' S c₂) s i = x s i :=
rfl

lemma injective_cast_le [fact (c₁ ≤ c₂)] :
  function.injective (Mbar_le.cast_le : Mbar_le r' S c₁ → Mbar_le r' S c₂) :=
λ x y h,
begin
  ext s n,
  change x.cast_le s n = y.cast_le s n,
  rw h,
end

@[ext] lemma ext (x y : Mbar_le r' S c) (h : ⇑x = y) : x = y :=
by { ext:2, exact h }

instance : has_zero (Mbar_le r' S c) := ⟨⟨0, zero_mem_filtration _⟩⟩

instance : inhabited (Mbar_le r' S c) := ⟨0⟩

end Mbar_le

variables (c₃)

/-- The addition on `Mbar_le`.
This addition is not homogeneous, but has type
`(Mbar_le r' S c₁) → (Mbar_le r' S c₂) → (Mbar_le r' S c₃)`
for `c₁ + c₂ ≤ c₃`. -/
def Mbar_le.add [h : fact (c₁ + c₂ ≤ c₃)]
  (F : Mbar_le r' S c₁) (G : Mbar_le r' S c₂) :
  Mbar_le r' S c₃ :=
subtype.mk (F + G) $ filtration_mono h.out $ add_mem_filtration F.mem_filtration G.mem_filtration

/-- An uncurried version of addition on `Mbar_le`,
meaning that it takes only 1 input, coming from a product type. -/
def Mbar_le.add' [fact (c₁ + c₂ ≤ c₃)] :
  Mbar_le r' S c₁ × Mbar_le r' S c₂ → Mbar_le r' S c₃ :=
λ x, Mbar_le.add c₃ x.1 x.2

-- TODO: register this as an instance??
/-- The negation on `Mbar_le`. -/
def Mbar_le.neg (F : Mbar_le r' S c) : Mbar_le r' S c :=
subtype.mk (-F) $ neg_mem_filtration F.mem_filtration

namespace Mbar_le

/-- The truncation map from Mbar_le to `Mbar_bdd`. -/
@[simps] def truncate (M : ℕ) (F : Mbar_le r' S c) : Mbar_bdd r' ⟨S⟩ c M :=
{ to_fun := λ s n, F s n,
  coeff_zero' := by simp,
  sum_le' :=
  begin
    refine le_trans _ F.mem_filtration,
    apply finset.sum_le_sum,
    rintros (s : S) -,
    rw fin.sum_univ_eq_sum_range (λ i, (↑(F s i).nat_abs * r' ^i)) (M+1),
    exact sum_le_tsum _ (λ _ _, subtype.property (_ : ℝ≥0)) (F.summable s),
  end }

lemma truncate_surjective (M : ℕ) :
  function.surjective (truncate M : Mbar_le r' S c → Mbar_bdd r' ⟨S⟩ c M) :=
begin
  intro x,
  have aux : _ := _,
  let F : Mbar_le r' S c :=
  ⟨{ to_fun := λ s n, if h : n < M + 1 then x s ⟨n, h⟩ else 0,
     summable' := aux, .. }, _⟩,
  { use F, ext s i, simp only [truncate_to_fun], dsimp,
    rw dif_pos i.is_lt, simp only [fin.eta] },
  { intro s, rw dif_pos (nat.zero_lt_succ _), exact x.coeff_zero s },
  { apply le_trans _ x.sum_le,
    apply finset.sum_le_sum,
    rintro s -,
    rw [← sum_add_tsum_nat_add' (M + 1), tsum_eq_zero, add_zero],
    { rw ← fin.sum_univ_eq_sum_range,
      apply finset.sum_le_sum,
      rintro i -,
      simp only [dif_pos i.is_lt, fin.eta, Mbar.coe_mk] },
    { intro i,
      dsimp,
      rw [dif_neg, int.nat_abs_zero, nat.cast_zero, zero_mul],
      linarith },
    { dsimp, apply aux } },
  { intro s,
    apply @summable_of_ne_finset_zero _ _ _ _ _ (finset.range (M+1)),
    intros i hi,
    rw finset.mem_range at hi,
    simp only [hi, zero_mul, dif_neg, not_false_iff, nat.cast_zero, int.nat_abs_zero] }
end

/-- Injectivity of the map `Mbar_le` to the limit of the `Mbar_bdd`. -/
lemma eq_iff_truncate_eq (x y : Mbar_le r' S c)
  (cond : ∀ M, truncate M x = truncate M y) : x = y :=
begin
  ext s n,
  change (truncate n x).1 s ⟨n, by linarith⟩ = (truncate n y).1 s ⟨n,_⟩,
  rw cond,
end

lemma truncate_cast_le (M : ℕ) [hc : fact (c₁ ≤ c₂)] (x : Mbar_le r' S c₁) :
  truncate M (Mbar_le.cast_le x : Mbar_le r' S c₂) = Mbar_bdd.cast_le (truncate M x) :=
rfl

/-- Underlying function of the element of `Mbar_le r' S c` associated to a sequence of
  elements of the truncated Mbars. -/
def mk_seq (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M) : S → ℕ → ℤ :=
λ s n, (T n).1 s ⟨n, lt_add_one n⟩

@[simp] lemma mk_seq_zero {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M} (s : S) : mk_seq T s 0 = 0 :=
(T 0).coeff_zero s

lemma mk_seq_eq_of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M)
  {s : S} {n : ℕ} {M : ℕ} (hnM : n < M + 1) :
  mk_seq T s n = (T M).1 s ⟨n, hnM⟩ :=
begin
  have hnM : n ≤ M := nat.lt_succ_iff.mp hnM,
  unfold mk_seq,
  rw ← compat n M hnM,
  apply Mbar_bdd.transition_eq,
end

lemma mk_seq_sum_range_eq (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M)
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (s : S) (n) :
  ∑ i in finset.range (n+1), (↑(mk_seq T s i).nat_abs * r'^i) =
  ∑ i : fin (n+1), (↑((T n).1 s i).nat_abs * r'^(i:ℕ)) :=
begin
  rw ← fin.sum_univ_eq_sum_range,
  congr',
  ext ⟨i, hi⟩,
  congr',
  exact mk_seq_eq_of_compat compat _,
end

lemma mk_seq_summable {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (s : S) :
  summable (λ (n : ℕ), (↑(mk_seq T s n).nat_abs * r' ^ n)) :=
begin
  apply @nnreal.summable_of_sum_range_le _ c,
  rintro (_|n),
  { simp only [finset.sum_empty, finset.range_zero, zero_le'] },
  { rw mk_seq_sum_range_eq T compat s n,
    refine le_trans _ (T n).sum_le,
    refine finset.single_le_sum (λ _ _, _) (finset.mem_univ s),
    apply zero_le' },
end

open filter

lemma mk_seq_tendsto {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) :
  tendsto (λ (n : ℕ), ∑ (s : S), ∑  i in finset.range n, (↑(mk_seq T s i).nat_abs * r'^i))
  at_top (nhds $ ∑ (s : S), ∑' n, (↑(mk_seq T s n).nat_abs * r'^n)) :=
tendsto_finset_sum _ $ λ s _, has_sum.tendsto_sum_nat $ summable.has_sum $ mk_seq_summable compat s

lemma mk_seq_sum_le {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) :
  (∑ s, ∑' (n : ℕ), (↑(mk_seq T s n).nat_abs * r' ^ n)) ≤ c :=
begin
  refine le_of_tendsto (mk_seq_tendsto compat) (eventually_of_forall _),
  rintro (_|n),
  { simp only [finset.sum_empty, finset.range_zero, finset.sum_const_zero, zero_le'] },
  { convert (T n).sum_le,
    funext,
    rw mk_seq_sum_range_eq T compat s n,
    refl }
end

lemma truncate_mk_seq {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (M : ℕ) :
  truncate M ⟨⟨mk_seq T, mk_seq_zero, mk_seq_summable compat⟩, mk_seq_sum_le compat⟩ = T M :=
begin
  ext s ⟨i, hi⟩,
  exact mk_seq_eq_of_compat compat _,
end

/-- `of_compat hT` is the limit of a compatible family `T M : Mbar_bdd r' ⟨S⟩ c M`.
This realizes `Mbar_le` as the profinite limit of the spaces `Mbar_bdd`,
see also `Mbar_le.eqv`. -/
def of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) : Mbar_le r' S c :=
⟨⟨mk_seq T, mk_seq_zero, mk_seq_summable compat⟩, mk_seq_sum_le compat⟩

@[simp] lemma truncate_of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (M : ℕ) :
  truncate M (of_compat compat) = T M :=
begin
  ext s ⟨i, hi⟩,
  exact mk_seq_eq_of_compat compat _,
end

/-- The equivalence (as types) between `Mbar_le r' S c`
and the profinite limit of the spaces `Mbar_bdd r' ⟨S⟩ c M`. -/
def eqv : Mbar_le r' S c ≃ Mbar_bdd.limit r' ⟨S⟩ c :=
{ to_fun := λ F, ⟨λ N, truncate _ F, by { intros, refl }⟩,
  inv_fun := λ F, of_compat F.2,
  left_inv := λ x, by { ext, refl },
  right_inv := by { rintro ⟨x, hx⟩, simp only [truncate_of_compat], } }

section topological_structure

instance : topological_space (Mbar_le r' S c) := topological_space.induced eqv (by apply_instance)

lemma is_open_iff {U : set (Mbar_bdd.limit r' ⟨S⟩ c)} : is_open (eqv ⁻¹' U) ↔ is_open U :=
begin
  rw is_open_induced_iff,
  have := function.surjective.preimage_injective (equiv.surjective (eqv : Mbar_le r' S c ≃ _)),
  simp only [iff_self, this.eq_iff],
  simp only [exists_eq_right],
end

/-- The homeomorphism between `Mbar_le r' S c`
and the profinite limit of the spaces `Mbar_bdd r' ⟨S⟩ c M`.

This is `Mbar_le.eqv`, lifted to a homeomorphism by transporting
the topology from the profinite limit to `Mbar_le`. -/
def homeo : Mbar_le r' S c ≃ₜ Mbar_bdd.limit r' ⟨S⟩ c :=
{ continuous_to_fun := begin
    simp only [equiv.to_fun_as_coe, continuous_def],
    intros U hU,
    rwa is_open_iff
  end,
  continuous_inv_fun := begin
    simp only [equiv.to_fun_as_coe, continuous_def],
    intros U hU,
    erw [← eqv.image_eq_preimage, ← is_open_iff],
    rwa eqv.preimage_image U,
  end,
  ..eqv }

lemma truncate_eq (M : ℕ) :
  (truncate M : Mbar_le r' S c → Mbar_bdd r' ⟨S⟩ c M) = (Mbar_bdd.proj M) ∘ homeo := rfl

instance : t2_space (Mbar_le r' S c) :=
⟨λ x y h, separated_by_continuous homeo.continuous (λ c, h $ homeo.injective c)⟩

instance [fact (0 < r')] : compact_space (Mbar_le r' S c) :=
begin
  constructor,
  rw homeo.embedding.is_compact_iff_is_compact_image,
  simp only [set.image_univ, homeomorph.range_coe],
  obtain ⟨h⟩ := (by apply_instance : compact_space (Mbar_bdd.limit r' ⟨S⟩ c)),
  exact h,
end

instance : totally_disconnected_space (Mbar_le r' S c) :=
{ is_totally_disconnected_univ :=
  begin
    rintros A - hA,
    suffices subsing : (homeo '' A).subsingleton,
    { intros x hx y hy, apply_rules [homeo.injective, subsing, set.mem_image_of_mem] },
    obtain ⟨h⟩ := (by apply_instance : totally_disconnected_space (Mbar_bdd.limit r' ⟨S⟩ c)),
    exact h _ (by tauto) (is_preconnected.image hA _ homeo.continuous.continuous_on)
  end }

lemma continuous_iff {α : Type*} [topological_space α] (f : α → Mbar_le r' S c) :
  continuous f ↔ (∀ M, continuous ((truncate M) ∘ f)) :=
begin
  split,
  { intros hf M,
    rw [truncate_eq, function.comp.assoc],
    revert M,
    rw ← Mbar_bdd.continuous_iff,
    refine continuous.comp homeo.continuous hf },
  { intro h,
    suffices : continuous (homeo ∘ f), by rwa homeo.comp_continuous_iff at this,
    rw Mbar_bdd.continuous_iff,
    exact h }
end

lemma continuous_truncate {M} : continuous (@truncate r' S _ c M) :=
(continuous_iff id).mp continuous_id _

lemma continuous_add' :
  continuous (Mbar_le.add' (c₁ + c₂) : Mbar_le r' S c₁ × Mbar_le r' S c₂ → Mbar_le r' S (c₁+c₂)) :=
begin
  rw continuous_iff,
  intros M,
  have : truncate M ∘ (λ x : Mbar_le r' S c₁ × Mbar_le r' S c₂, Mbar_le.add _ x.1 x.2) =
    (λ x : (Mbar_le r' S c₁ × Mbar_le r' S c₂), Mbar_bdd.add (truncate M x.1) (truncate M x.2)) :=
    by {ext; refl},
  erw this,
  suffices : continuous (λ x : Mbar_bdd r' ⟨S⟩ c₁ M × Mbar_bdd r' ⟨S⟩ c₂ M, Mbar_bdd.add x.1 x.2),
  { have claim : (λ x : (Mbar_le r' S c₁ × Mbar_le r' S c₂),
      Mbar_bdd.add (truncate M x.1) (truncate M x.2)) =
      (λ x : Mbar_bdd r' ⟨S⟩ c₁ M × Mbar_bdd r' ⟨S⟩ c₂ M, Mbar_bdd.add x.1 x.2) ∘
      (λ x : Mbar_le r' S c₁ × Mbar_le r' S c₂, (truncate M x.1, truncate M x.2)), by {ext, refl},
    rw claim,
    refine continuous.comp this _,
    refine continuous.prod_map continuous_truncate continuous_truncate },
  exact continuous_of_discrete_topology,
end

lemma continuous_neg : continuous (Mbar_le.neg : Mbar_le r' S c → Mbar_le r' S c) :=
begin
  rw continuous_iff,
  intro M,
  change continuous (λ x : Mbar_le r' S c, Mbar_bdd.neg (truncate M x)),
  exact continuous.comp continuous_of_discrete_topology continuous_truncate,
end

end topological_structure

lemma continuous_cast_le (r' : ℝ≥0) (S : Type u) [fintype S] (c₁ c₂ : ℝ≥0) [hc : fact (c₁ ≤ c₂)] :
  continuous (@Mbar_le.cast_le r' S _ c₁ c₂ _) :=
begin
  rw continuous_iff,
  intro M,
  simp only [function.comp, truncate_cast_le],
  exact continuous_bot.comp continuous_truncate
end

lemma continuous_of_normed_group_hom
  (f : (Mbar r' S) →+ (Mbar r' S))
  (g : Mbar_le r' S c₁ → Mbar_le r' S c₂)
  (h : ∀ x, ↑(g x) = f x)
  (H : ∀ M, ∃ N, ∀ (F : Mbar r' S),
    (∀ s i, i < N + 1 → F s i = 0) → (∀ s i, i < M + 1 → f F s i = 0)) :
  continuous g :=
begin
  rw continuous_iff,
  intros M,
  rcases H M with ⟨N, hN⟩,
  let φ : Mbar_bdd r' ⟨S⟩ c₁ N → Mbar_le r' S c₁ :=
    classical.some (truncate_surjective N).has_right_inverse,
  have hφ : function.right_inverse φ (truncate N) :=
    classical.some_spec (truncate_surjective N).has_right_inverse,
  suffices : truncate M ∘ g = truncate M ∘ g ∘ φ ∘ truncate N,
  { rw [this, ← function.comp.assoc, ← function.comp.assoc],
    apply continuous_bot.comp continuous_truncate },
  ext1 x,
  suffices : ∀ s i, i < M + 1 → (g x) s i = (g (φ (truncate N x))) s i,
  { ext s i, dsimp [function.comp], apply this, exact i.property },
  intros s i hi,
  rw [← coe_coe_to_fun, h, ← coe_coe_to_fun, h, ← sub_eq_zero],
  show ((f x) - f (φ (truncate N x))) s i = 0,
  rw [← f.map_sub],
  apply hN _ _ _ _ hi,
  clear hi i s, intros s i hi,
  simp only [Mbar.coe_sub, pi.sub_apply, sub_eq_zero],
  suffices : ∀ s i, (truncate N x) s i = truncate N (φ (truncate N x)) s i,
  { exact this s ⟨i, hi⟩ },
  intros s i, congr' 1,
  rw hφ (truncate N x)
end

/-- Construct a map between `Mbar_le r' S c₁` and `Mbar_le r' S c₂`
from a bounded group homomorphism `Mbar r' S → Mbar r' S`.

If `f` satisfies a suitable criterion,
then the constructed map is continuous for the profinite topology;
see `continuous_of_normed_group_hom`. -/
def hom_of_normed_group_hom {C : ℝ≥0} (c₁ c₂ : ℝ≥0) [hc : fact (C * c₁ ≤ c₂)]
  (f : Mbar r' S →+ Mbar r' S) (h : f ∈ filtration (Mbar r' S →+ Mbar r' S) C)
  (F : Mbar_le r' S c₁) :
  Mbar_le r' S c₂ :=
⟨{ to_fun := λ s i, f F s i,
  coeff_zero' := Mbar.coeff_zero _,
  summable' := Mbar.summable _ },
  filtration_mono hc.out (h F.mem_filtration)⟩

lemma continuous_hom_of_normed_group_hom {C : ℝ≥0} (c₁ c₂ : ℝ≥0)
  [hc : fact (C * c₁ ≤ c₂)]
  (f : Mbar r' S →+ Mbar r' S) (h : f ∈ filtration (Mbar r' S →+ Mbar r' S) C)
  (H : ∀ M, ∃ N, ∀ (F : Mbar r' S),
    (∀ s i, i < N + 1 → F s i = 0) → (∀ s i, i < M + 1 → f F s i = 0)) :
  continuous (hom_of_normed_group_hom c₁ c₂ f h) :=
continuous_of_normed_group_hom f _ (λ F, by { ext, refl }) H

@[simp] lemma coe_hom_of_normed_group_hom_apply {C : ℝ≥0} (c₁ c₂ : ℝ≥0)
  [hc : fact (C * c₁ ≤ c₂)]
  (f : Mbar r' S →+ Mbar r' S) (h : f ∈ filtration (Mbar r' S →+ Mbar r' S) C)
  (F : (Mbar_le r' S c₁)) (s : S) (i : ℕ) :
  (hom_of_normed_group_hom c₁ c₂ f h) F s i = f F s i := rfl

section Tinv

/-!
### The action of T⁻¹
-/

/-- The action of `T⁻¹` as map `Mbar_le r S c₁ → Mbar_le r S c₂`.

This action is induced by the action of `T⁻¹` on power series modulo constants: `ℤ⟦T⟧/ℤ`.
So `T⁻¹` sends `T^(n+1)` to `T^n`, but `T^0 = 0`. -/
def Tinv {r : ℝ≥0} {S : Type u} [fintype S] {c₁ c₂ : ℝ≥0} [fact (0 < r)] [fact (r⁻¹ * c₁ ≤ c₂)] :
  Mbar_le r S c₁ → Mbar_le r S c₂ :=
hom_of_normed_group_hom c₁ c₂ Mbar.Tinv Mbar.Tinv_mem_filtration

@[simp] lemma Tinv_apply {r : ℝ≥0} {S : Type u} [fintype S] {c₁ c₂ : ℝ≥0}
  [fact (0 < r)] [fact (r⁻¹ * c₁ ≤ c₂)] (F : Mbar_le r S c₁) (s : S) (i : ℕ) :
  (Tinv F : Mbar_le r S c₂) s i = Mbar.Tinv (F : Mbar r S) s i :=
rfl

lemma continuous_Tinv (r : ℝ≥0) (S : Type u) [fintype S] (c₁ c₂ : ℝ≥0)
  [fact (0 < r)] [fact (r⁻¹ * c₁ ≤ c₂)] :
  continuous (@Tinv r S _ c₁ c₂ _ _) :=
continuous_hom_of_normed_group_hom c₁ c₂ _ Mbar.Tinv_mem_filtration $
begin
  intros M,
  use M+1,
  rintro F hF s (_|i) hi,
  { simp only [Mbar.Tinv, add_monoid_hom.mk'_apply, Mbar.coe_mk, Mbar.Tinv_aux_zero] },
  { simp only [Mbar.Tinv, Mbar.Tinv_aux_succ, add_monoid_hom.mk'_apply, Mbar.coe_mk],
    apply hF,
    exact nat.succ_lt_succ hi },
end

end Tinv

end Mbar_le

-- move this up a bit
instance [fact (0 < r')] : profinitely_filtered_pseudo_normed_group (Mbar r' S) :=
{ topology := λ c, show topological_space (Mbar_le r' S c), by apply_instance,
  t2 := λ c, show t2_space (Mbar_le r' S c), by apply_instance,
  td := λ c, show totally_disconnected_space (Mbar_le r' S c), by apply_instance,
  compact := λ c, show compact_space (Mbar_le r' S c), by apply_instance,
  continuous_add' := λ c₁ c₂, Mbar_le.continuous_add',
  continuous_neg' := λ c, Mbar_le.continuous_neg,
  continuous_cast_le := λ c₁ c₂,
  begin
    introI h,
    rw show pseudo_normed_group.cast_le = (Mbar_le.cast_le : Mbar_le r' S c₁ → Mbar_le r' S c₂),
      by {ext, refl},
    exact Mbar_le.continuous_cast_le r' S c₁ c₂,
  end,
  .. Mbar.pseudo_normed_group }

#lint-
