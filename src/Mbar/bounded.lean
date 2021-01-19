import data.fintype.intervals
import data.real.basic
import algebra.big_operators.ring
import data.fintype.card
import category_theory.Fintype
import topology.order
import topology.separation
import topology.subset_properties
import data.real.nnreal

noncomputable theory
open_locale big_operators classical nnreal

-- Thanks to Ruben Van de Velde and Yury G. Kudryashov for help with
-- the Ico_finite and Icc_finite lemmas.
-- TODO: Move these somewhere...
open set
lemma Ico_finite (a b : ℤ) : set.finite (Ico a b) := ⟨set.Ico_ℤ_fintype a b⟩
lemma Icc_finite (a b : ℤ) : set.finite (Icc a b) :=
begin
  convert Ico_finite a (b+1),
  ext,
  simp [int.lt_add_one_iff],
end

instance (a b : ℤ) : fintype (Icc a b) := nonempty.some (Icc_finite a b)

structure Mbar_bdd (r : ℝ≥0) (S : Fintype) (c : ℝ≥0) (M : ℕ) :=
(to_fun : S → fin (M + 1) → ℤ)
(coeff_zero' : ∀ s, to_fun s 0 = 0)
(sum_le' : (∑ s i, (↑(to_fun s i).nat_abs * r^(i : ℕ))) ≤ c)

namespace Mbar_bdd

variables {r : ℝ≥0} {S : Fintype} {c c₁ c₂ : ℝ≥0} {M : ℕ}

instance has_coe_to_fun : has_coe_to_fun (Mbar_bdd r S c M) := ⟨_, Mbar_bdd.to_fun⟩

@[simp] lemma coe_mk (x h₁ h₂) : ((⟨x, h₁, h₂⟩ : Mbar_bdd r S c M) : S → ℕ → ℤ) = x := rfl

@[simp] protected lemma coeff_zero (x : Mbar_bdd r S c M) (s : S) : x s 0 = 0 := x.coeff_zero' s

protected lemma sum_le (x : Mbar_bdd r S c M) :
  (∑ s i, ((↑(x s i).nat_abs * r^(i:ℕ)))) ≤ c := x.sum_le'

protected def cast_le [hc : fact (c₁ ≤ c₂)] (x : Mbar_bdd r S c₁ M) : Mbar_bdd r S c₂ M :=
⟨x.1, x.coeff_zero, x.sum_le.trans hc⟩

def mk' (x : S → fin (M + 1) → ℤ)
  (h : (∀ s, x s 0 = 0) ∧
       (∑ s i, ((↑(x s i).nat_abs * r^(i:ℕ)))) ≤ c) :
  Mbar_bdd r S c M :=
{ to_fun := x, coeff_zero' := h.1, sum_le' := h.2 }

@[ext] lemma ext (x y : Mbar_bdd r S c M) (h : ⇑x = y) : x = y :=
by { cases x, cases y, congr, exact h }

instance : has_zero (Mbar_bdd r S c M) :=
{ zero :=
  { to_fun := 0,
    coeff_zero' := λ s, rfl,
    sum_le' :=
    by simp only [zero_mul, pi.zero_apply, finset.sum_const_zero,
      nat.cast_zero, zero_le', int.nat_abs_zero] } }

open finset

lemma coeff_bound [h0r : fact (0 < r)] (F : S → fin (M + 1) → ℤ)
  (hF : ∑ s i, (↑(F s i).nat_abs * r^(i : ℕ)) ≤ c) (n : fin (M + 1)) (s : S) :
  ↑(F s n).nat_abs ≤ c / min (r ^ M) 1 :=
begin
  rw [div_eq_mul_inv],
  apply le_mul_inv_of_mul_le ((lt_min (pow_pos h0r _) zero_lt_one).ne.symm),
  calc ↑(F s n).nat_abs * min (r ^ M) 1 ≤ ↑(F s n).nat_abs * r ^ (n:ℕ) : begin
    refine mul_le_mul_of_nonneg_left _ (subtype.property (_ : ℝ≥0)),
    cases le_or_lt r 1 with hr1 hr1,
    { refine le_trans (min_le_left _ _) _,
      exact pow_le_pow_of_le_one (le_of_lt h0r) hr1 (nat.lt_add_one_iff.1 n.2) },
    { exact le_trans (min_le_right _ _) (one_le_pow_of_one_le (le_of_lt hr1) _) },
  end
  -- ... = (↑(F s n).nat_abs * r ^ (n:ℕ)) : by {  } --rw [abs_mul, abs_of_pos (pow_pos h0r _)]
  ... ≤ ∑ i, (↑(F s i).nat_abs * r ^ (i:ℕ)) :
    single_le_sum (λ (i : fin (M + 1)) _, _) (mem_univ n)
  ... ≤ ∑ s i, (↑(F s i).nat_abs * r^(i : ℕ)) : begin
    refine single_le_sum (λ _ _, _) (mem_univ s),
    exact sum_nonneg (λ _ _, (subtype.property (_ : ℝ≥0))),
  end
  ... ≤ c : hF,
  apply subtype.property (_ : ℝ≥0)
end

-- move this
lemma cast_nat_abs {R : Type*} [linear_ordered_ring R] : ∀ (n : ℤ), (n.nat_abs : R) = abs n
| (n : ℕ) := by simp only [int.nat_abs_of_nat, int.cast_coe_nat, nat.abs_cast]
| -[1+n]  := by simp only [int.nat_abs, int.cast_neg_succ_of_nat, abs_neg,
                           ← nat.cast_succ, nat.abs_cast]

lemma cast_nat_abs_eq_nnabs_cast (n : ℤ) :
  (n.nat_abs : ℝ≥0) = real.nnabs n :=
by { ext, rw [nnreal.coe_nat_cast, cast_nat_abs, nnreal.coe_nnabs] }

private def temp_map [fact (0 < r)] (F : Mbar_bdd r S c M) (n : fin (M + 1)) (s : S) :
  Icc (ceil (-(c / min (r ^ M) 1) : ℝ)) (floor (c / min (r ^ M) 1 : ℝ)) :=
begin
  have h : (-(c / min (r ^ M) 1) : ℝ) ≤ F s n ∧ (F s n : ℝ) ≤ (c / min (r ^ M) 1 : ℝ),
  { rw [← abs_le, ← nnreal.coe_nnabs, ← cast_nat_abs_eq_nnabs_cast, nnreal.coe_nat_cast],
    norm_cast, exact coeff_bound F F.sum_le n s },
  exact ⟨F s n, ceil_le.2 $ h.1, le_floor.2 h.2⟩
end

instance [fact (0 < r)] : fintype (Mbar_bdd r S c M) :=
fintype.of_injective temp_map begin
  rintros ⟨f1, hf1, hf1'⟩ ⟨f2, hf2, hf2'⟩ h,
  ext s n,
  change (temp_map ⟨f1, hf1, hf1'⟩ n s).1 = (temp_map ⟨f2, hf2, hf2'⟩ n s).1,
  rw h,
end

def ι {M N : ℕ} (h : M ≤ N) : fin M ↪ fin N := (fin.cast_le h).to_embedding

-- Should this be in mathlib?
lemma sum_eq_sum_map_ι {M N : ℕ} (h : M ≤ N) (f : fin N → ℝ≥0) :
  ∑ i, f (ι h i) = ∑ j in finset.map (ι h) finset.univ, f j :=
finset.sum_bij' (λ a _, ι h a) (λ a ha, by {rw mem_map, exact ⟨a, ha, rfl⟩})
(λ a ha, rfl) (λ a ha, ⟨a.1, begin
  rcases finset.mem_map.mp ha with ⟨⟨w,ww⟩,hw,rfl⟩,
  change w < M,
  linarith,
end ⟩)
(λ a ha, finset.mem_univ _) (λ a ha, by tidy) (λ a ha, by tidy)

/-- The transition maps between the Mbar_bdd sets. -/
def transition (r : ℝ≥0) {S : Fintype} {c : ℝ≥0} {M N : ℕ} (h : M ≤ N) (x : Mbar_bdd r S c N) :
  Mbar_bdd r S c M :=
{ to_fun := λ s i, x s (ι (add_le_add_right h 1) i),
  coeff_zero' := λ s, x.coeff_zero _,
  sum_le' :=
  begin
    refine le_trans _ x.sum_le,
    apply finset.sum_le_sum,
    intros s hs,
    let I := finset.map (ι (by linarith : M+1 ≤ N+1))
      (finset.univ : finset (fin (M+1))),
    refine le_trans _
      (finset.sum_le_sum_of_subset_of_nonneg (finset.subset_univ I) _),
    { rw ← sum_eq_sum_map_ι,
      apply le_of_eq,
      congr },
    { intros, exact subtype.property (_ : ℝ≥0) }
  end }

lemma transition_eq {r : ℝ≥0} {S : Fintype} {c : ℝ≥0} {M N : ℕ} (h : M ≤ N)
  (F : Mbar_bdd r S c N) (s : S) (i : fin (M+1)) :
  (transition r h F).1 s i = F.1 s (ι (by linarith) i) := by tidy

lemma transition_transition {r : ℝ≥0} {S : Fintype} {c : ℝ≥0}
  {M N K : ℕ} (h : M ≤ N) (hh : N ≤ K) (x : Mbar_bdd r S c K) :
  transition r h (transition r hh x) = transition r (le_trans h hh) x := by tidy

lemma transition_cast_le {N : ℕ} (h : M ≤ N) [hc : fact (c₁ ≤ c₂)] (x : Mbar_bdd r S c₁ N) :
  transition r h (@Mbar_bdd.cast_le r S c₁ c₂ N _ x) =
    Mbar_bdd.cast_le (transition r h x) :=
by { ext, refl }

@[reducible] def limit (r S c) :=
{ F : Π (M : ℕ), Mbar_bdd r S c M // ∀ (M N : ℕ) (h : M ≤ N), transition r h (F N) = F M }

def emb_aux : limit r S c → (Π (M : ℕ), Mbar_bdd r S c M) := coe

section topological_structure

instance : topological_space (Mbar_bdd r S c M) := ⊥
instance : discrete_topology (Mbar_bdd r S c M) := ⟨rfl⟩

-- sanity check
example : t2_space (limit r S c) := by apply_instance
example : totally_disconnected_space (limit r S c) := by apply_instance
example [fact (0 < r)] : compact_space (Mbar_bdd r S c M) := by apply_instance

def Γ : Π (m n : ℕ) (h : m ≤ n), set (Π (M : ℕ), Mbar_bdd r S c M) := λ m n h,
  { F | transition r h (F n) = F m }

def Γ₀ : Π (m n : ℕ) (h : m ≤ n), set (Mbar_bdd r S c m × Mbar_bdd r S c n) := λ m n h,
  { a | transition r h a.2 = a.1 }

def π : Π (m : ℕ), (Π (M : ℕ), Mbar_bdd r S c M) → Mbar_bdd r S c m := λ m F, F m

def π₂ : Π (m n : ℕ), (Π (M : ℕ), Mbar_bdd r S c M) → Mbar_bdd r S c m × Mbar_bdd r S c n :=
  λ m n F, ⟨F m, F n⟩

lemma range_emb_aux_eq : range (@emb_aux r S c) = ⋂ (x : {y : ℕ × ℕ // y.1 ≤ y.2}), Γ x.1.1 x.1.2 x.2 :=
  set.ext $ λ x, iff.intro (λ ⟨w,hx⟩ y ⟨z,hz⟩, hz ▸ hx ▸ w.2 _ _ _)
  (λ h0, ⟨⟨x,λ m n h1, h0 _ ⟨⟨⟨m,n⟩,h1⟩,rfl⟩⟩, rfl⟩)

lemma π_continuous {m : ℕ} : continuous (π m : _ → Mbar_bdd r S c m) := continuous_apply _

lemma π₂_eq {m n : ℕ} : (π₂ m n : _ → Mbar_bdd r S c m × _) = (λ x, ⟨x m, x n⟩) :=
by {ext; refl}

lemma π₂_continuous {m n : ℕ} : continuous (π₂ m n : _ → Mbar_bdd r S c _ × _) :=
by {rw π₂_eq, exact continuous.prod_mk π_continuous π_continuous}

lemma emb (r S c) : closed_embedding (@emb_aux r S c) :=
{ induced := rfl,
  inj := by tidy,
  closed_range := begin
    rw range_emb_aux_eq,
    apply is_closed_Inter,
    rintros ⟨⟨m, n⟩, h0⟩,
    rw (show (Γ m n h0 : set (Π M, Mbar_bdd r S c M)) = π₂ m n ⁻¹' (Γ₀ m n h0), by tauto),
    refine is_closed.preimage π₂_continuous (is_closed_discrete _),
  end }

instance [fact (0 < r)] : compact_space (limit r S c) :=
begin
  erw [← compact_iff_compact_space, compact_iff_compact_univ, compact_iff_compact_in_subtype],
  apply is_closed.compact,
  exact embedding_is_closed (emb r S c).to_embedding (emb r S c).closed_range is_closed_univ,
end

def proj (M : ℕ) : Mbar_bdd.limit r S c → Mbar_bdd r S c M := λ F, F.1 M

lemma proj_eq (M : ℕ) : (proj M : _ → Mbar_bdd r S c _) = (π M) ∘ emb_aux := rfl

lemma continuous_iff {α : Type*} [topological_space α] (f : α → Mbar_bdd.limit r S c) :
  continuous f ↔ (∀ (M : ℕ), continuous ((proj M) ∘ f)) :=
begin
  split,
  { intros hf M,
    refine continuous.comp _ hf,
    rw proj_eq,
    exact continuous.comp π_continuous (emb _ _ _).continuous },
  { intros h,
    rw [embedding.continuous_iff (emb r S c).to_embedding],
    exact continuous_pi h }
end

end topological_structure

section addition

def add (F : Mbar_bdd r S c₁ M) (G : Mbar_bdd r S c₂ M) : Mbar_bdd r S (c₁ + c₂) M :=
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

end addition

end Mbar_bdd

#lint- only unused_arguments def_lemma doc_blame
