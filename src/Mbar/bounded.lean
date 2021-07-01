import data.fintype.intervals
import data.real.basic
import algebra.big_operators.ring
import data.fintype.card
import category_theory.Fintype
import topology.order
import topology.separation
import topology.subset_properties
import data.real.nnreal

import for_mathlib.nat_abs

/-!

# \overline{\mathcal{M}}_r(S)_{\leq c}

Throughout, `S` is finite (not profinite).

`ℳ-bar_{r'}(S)_{≤c}` is the filtration on `ℳ-bar_{r'}(S)` by profinite subsets described
at the beginning of section 9 of `analytic.pdf`. It's defined not as a subset
of `ℳ-bar_{r'}(S)` but as an independent type. It's a projective limit of
types `Mbar_bdd r' S c M` which have an additional hypothesis that the power
series involved are actually polynomials of degree at most `M`.

## Main definitions

- `Mbar_bdd r' S c M`: the subset of `S → Tℤ[[T]]/(T^{M+1})` consisting of
  elements `F_s = ∑_{n=1}^M a_{n,s} T^n` such that `∑_{s,n} |a_{n,s}| (r')^n ≤ c`.
- `Mbar_bdd.limit r' S c`: the projective limit of `Mbar_bdd r' S c M`, as a subtype
  of the product.

-/
noncomputable theory
open_locale big_operators classical nnreal
open set

/-- `Mbar_bdd r' S c M` is the subset of `S → Tℤ[[T]]/(T^{M+1})` consisting of elements
`F_s = ∑_{n=1}^M a_{n,s} T^n` such that `∑_{s,n} |a_{n,s}| r^n ≤ c`.
This is an auxiliary object used to define the profinite topology on `Mbar r' S`. -/
structure Mbar_bdd (r : ℝ≥0) (S : Fintype) (c : ℝ≥0) (M : ℕ) :=
(to_fun      : S → fin (M + 1) → ℤ)
(coeff_zero' : ∀ s, to_fun s 0 = 0)
(sum_le'     : (∑ s i, (↑(to_fun s i).nat_abs * r^(i : ℕ))) ≤ c)

namespace Mbar_bdd

variables {r' : ℝ≥0} {S : Fintype} {c c₁ c₂ : ℝ≥0} {M : ℕ}

instance has_coe_to_fun : has_coe_to_fun (Mbar_bdd r' S c M) := ⟨_, Mbar_bdd.to_fun⟩

@[simp] lemma coe_mk (x h₁ h₂) : ((⟨x, h₁, h₂⟩ : Mbar_bdd r' S c M) : S → ℕ → ℤ) = x := rfl

@[simp] protected lemma coeff_zero (x : Mbar_bdd r' S c M) (s : S) : x s 0 = 0 := x.coeff_zero' s

protected lemma sum_le (x : Mbar_bdd r' S c M) :
  (∑ s i, ((↑(x s i).nat_abs * r'^(i:ℕ)))) ≤ c := x.sum_le'

/-- The obvious map from `Mbar_bdd r' S c₁ M` to `Mbar_bdd r' S c₂ M`, for `c₁ ≤ c₂`. -/
protected def cast_le [hc : fact (c₁ ≤ c₂)] (x : Mbar_bdd r' S c₁ M) : Mbar_bdd r' S c₂ M :=
⟨x.1, x.coeff_zero, x.sum_le.trans hc.out⟩

@[ext] lemma ext (x y : Mbar_bdd r' S c M) (h : ⇑x = y) : x = y :=
by { cases x, cases y, congr, exact h }

instance : has_zero (Mbar_bdd r' S c M) :=
{ zero :=
  { to_fun := 0,
    coeff_zero' := λ s, rfl,
    sum_le' := by simp only [zero_mul, pi.zero_apply, finset.sum_const_zero,
      nat.cast_zero, zero_le', int.nat_abs_zero] } }

instance : inhabited (Mbar_bdd r' S c M) := ⟨0⟩

open finset

lemma coeff_bound [h0r : fact (0 < r')] (F : S → fin (M + 1) → ℤ)
  (hF : ∑ s i, (↑(F s i).nat_abs * r'^(i : ℕ)) ≤ c) (n : fin (M + 1)) (s : S) :
  ↑(F s n).nat_abs ≤ c / min (r' ^ M) 1 :=
begin
  rw [div_eq_mul_inv],
  apply le_mul_inv_of_mul_le ((lt_min (pow_pos h0r.out _) zero_lt_one).ne.symm),
  calc ↑(F s n).nat_abs * min (r' ^ M) 1 ≤ ↑(F s n).nat_abs * r' ^ (n:ℕ) : _ -- see below for proof
  ... ≤ ∑ i, (↑(F s i).nat_abs * r' ^ (i:ℕ)) :
    single_le_sum (λ (i : fin (M + 1)) _, _) (mem_univ n)
  ... ≤ ∑ s i, (↑(F s i).nat_abs * r'^(i:ℕ)) :
    by { refine single_le_sum (λ _ _, _) (mem_univ s),
      exact sum_nonneg (λ _ _, (subtype.property (_ : ℝ≥0))) }
  ... ≤ c : hF,
  { refine mul_le_mul_of_nonneg_left _ (subtype.property (_ : ℝ≥0)),
    cases le_or_lt r' 1 with hr1 hr1,
    { refine le_trans (min_le_left _ _) _,
      exact pow_le_pow_of_le_one h0r.out.le hr1 (nat.lt_add_one_iff.1 n.2) },
    { exact le_trans (min_le_right _ _) (one_le_pow_of_one_le (le_of_lt hr1) _) } },
  apply subtype.property (_ : ℝ≥0)
end

/-- An auxiliary function used to prove finiteness of `Mbar_bdd r' S c M`. -/
private def temp_map [fact (0 < r')] (F : Mbar_bdd r' S c M) (n : fin (M + 1)) (s : S) :
  Icc (ceil (-(c / min (r' ^ M) 1) : ℝ)) (floor (c / min (r' ^ M) 1 : ℝ)) :=
have h : (-(c / min (r' ^ M) 1) : ℝ) ≤ F s n ∧ (F s n : ℝ) ≤ (c / min (r' ^ M) 1 : ℝ),
by { rw [← abs_le, ← nnreal.coe_nnabs, ← cast_nat_abs_eq_nnabs_cast],
    exact_mod_cast coeff_bound F F.sum_le n s },
⟨F s n, ceil_le.2 $ h.1, le_floor.2 h.2⟩

instance [fact (0 < r')] : fintype (Mbar_bdd r' S c M) :=
fintype.of_injective temp_map
begin
  rintros ⟨f1, hf1, hf1'⟩ ⟨f2, hf2, hf2'⟩ h,
  ext s n,
  change (temp_map ⟨f1, hf1, hf1'⟩ n s).1 = (temp_map ⟨f2, hf2, hf2'⟩ n s).1,
  rw h,
end

/-- The transition map from `Mbar_bdd r' S c N` to `Mbar_bdd r' S c M`, given `M ≤ N`. -/
def transition (r' : ℝ≥0) {S : Fintype} {c : ℝ≥0} {M N : ℕ} (h : M ≤ N) (x : Mbar_bdd r' S c N) :
  Mbar_bdd r' S c M :=
{ to_fun := λ s i, x s (fin.cast_le (add_le_add_right h 1) i),
  coeff_zero' := λ s, x.coeff_zero _,
  sum_le' :=
  begin
    refine le_trans _ x.sum_le,
    apply finset.sum_le_sum,
    intros s hs,
    let I := finset.map (fin.cast_le (add_le_add_right h 1)).to_embedding
      (finset.univ : finset (fin (M+1))),
    refine le_trans _
      (finset.sum_le_sum_of_subset_of_nonneg (finset.subset_univ I) _),
    { rw finset.sum_map,
      apply le_of_eq,
      congr },
    { intros, exact subtype.property (_ : ℝ≥0) }
  end }

lemma transition_eq {r' : ℝ≥0} {S : Fintype} {c : ℝ≥0} {M N : ℕ} (h : M ≤ N)
  (F : Mbar_bdd r' S c N) (s : S) (i : fin (M+1)) :
  (transition r' h F).1 s i = F.1 s (fin.cast_le (add_le_add_right h 1) i) := rfl

lemma transition_transition {r' : ℝ≥0} {S : Fintype} {c : ℝ≥0}
  {M N K : ℕ} (h : M ≤ N) (hh : N ≤ K) (x : Mbar_bdd r' S c K) :
  transition r' h (transition r' hh x) = transition r' (le_trans h hh) x := rfl

lemma transition_cast_le {N : ℕ} (h : M ≤ N) [hc : fact (c₁ ≤ c₂)] (x : Mbar_bdd r' S c₁ N) :
  transition r' h (Mbar_bdd.cast_le x : Mbar_bdd r' S c₂ N) =
    Mbar_bdd.cast_le (transition r' h x) := rfl

/-- The limit of `Mbar_bdd r' S c M` along the `transition` maps as `M` increases. -/
abbreviation limit (r' S c) :=
{ F : Π (M : ℕ), Mbar_bdd r' S c M // ∀ (M N : ℕ) (h : M ≤ N), transition r' h (F N) = F M }

/-- The obvious embedding `Mbar_bdd.limit r' S c`
into the product of `Mbar_bdd r' S c M` as `M` varies. -/
def emb_aux : limit r' S c → (Π (M : ℕ), Mbar_bdd r' S c M) := coe

section topological_structure

instance : topological_space (Mbar_bdd r' S c M) := ⊥
instance : discrete_topology (Mbar_bdd r' S c M) := ⟨rfl⟩

-- sanity check
example : t2_space (limit r' S c) := by apply_instance
example : totally_disconnected_space (limit r' S c) := by apply_instance
example [fact (0 < r')] : compact_space (Mbar_bdd r' S c M) := by apply_instance

lemma emb (r' S c) : closed_embedding (@emb_aux r' S c) :=
{ induced := rfl,
  inj := subtype.coe_injective,
  closed_range :=
  begin
    have : range emb_aux = ⋂ (x : {y : ℕ × ℕ // y.1 ≤ y.2}),
      {F : Π M, Mbar_bdd r' S c M | transition r' x.2 (F x.val.2) = F x.val.1},
    { ext,
      simp only [emb_aux, prod.forall, mem_Inter, mem_set_of_eq,
        subtype.range_coe_subtype, subtype.forall], },
    rw this,
    apply is_closed_Inter,
    rintros ⟨⟨m, n⟩, h0 : m ≤ n⟩,
    refine is_closed_eq (continuous.comp _ $ continuous_apply _) (continuous_apply _),
    exact continuous_of_discrete_topology,
  end }

instance [fact (0 < r')] : compact_space (limit r' S c) :=
begin
  erw [← is_compact_iff_compact_space, is_compact_iff_is_compact_univ,
    compact_iff_compact_in_subtype],
  apply is_closed.is_compact,
  exact (emb r' S c).is_closed_map _ is_closed_univ
end

/-- The projection from `Mbar_bdd.limit r' S c M` to `Mbar_bdd r' S c M`.  -/
def proj (M : ℕ) : Mbar_bdd.limit r' S c → Mbar_bdd r' S c M := λ F, F.1 M

lemma continuous_iff {α : Type*} [topological_space α] (f : α → Mbar_bdd.limit r' S c) :
  continuous f ↔ (∀ (M : ℕ), continuous ((proj M) ∘ f)) :=
begin
  split,
  { intros hf M,
    exact continuous.comp ((continuous_apply _).comp continuous_subtype_val) hf, },
  { intros h,
    rw [embedding.continuous_iff (emb r' S c).to_embedding],
    exact continuous_pi h }
end

end topological_structure

section addition

/-- The addition on `Mbar_bdd r' S c M`.
It takes a term of type `Mbar_bdd r' S c₁ M` and a term of type `Mbar_bdd r' S c₂ M`
and produces a term of type `Mbar_bdd r' S (c₁ + c₂) M`. -/
def add (F : Mbar_bdd r' S c₁ M) (G : Mbar_bdd r' S c₂ M) : Mbar_bdd r' S (c₁ + c₂) M :=
{ to_fun := F + G,
  coeff_zero' := λ s, by simp,
  sum_le' :=
  begin
    refine le_trans _ (add_le_add F.sum_le G.sum_le),
    rw ← finset.sum_add_distrib,
    refine finset.sum_le_sum _,
    rintro s -,
    rw ← sum_add_distrib,
    refine finset.sum_le_sum _,
    rintro i -,
    rw ← add_mul,
    apply mul_le_mul_right',
    norm_cast,
    apply int.nat_abs_add_le
  end }

/-- Negation on `Mbar_bdd r' S c M` -/
def neg (F : Mbar_bdd r' S c M) : Mbar_bdd r' S c M :=
{ to_fun := -F,
  coeff_zero' := λ s, by simp,
  sum_le' := by { simp only [abs_neg, pi.neg_apply, int.nat_abs_neg], exact F.sum_le } }

end addition

end Mbar_bdd

#lint-
