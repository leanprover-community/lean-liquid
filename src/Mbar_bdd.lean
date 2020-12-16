import data.fintype.intervals
import data.real.basic
import algebra.big_operators.basic
import category_theory.Fintype
import topology.order
import topology.separation
import topology.subset_properties

noncomputable theory
open_locale big_operators classical

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

def Mbar_bdd (r : ℝ) (S : Fintype) (c : ℝ) (M : ℕ) :=
{F : S → fin (M + 1) → ℤ //
  (∀ s, F s 0 = 0) ∧
  (∑ s i, abs ((F s i : ℝ) * r ^ (i : ℕ)) ≤ c) }

namespace Mbar_bdd

variables {r : ℝ} {S : Fintype} {c : ℝ} {M : ℕ}

open finset

lemma nonneg_of_Mbar_bdd {r : ℝ} {S : Fintype} {c : ℝ} {M : ℕ}
  (x : Mbar_bdd r S c M) : 0 ≤ c :=
begin
  -- This should be a simple term-mode proof but I got a deterministic
  -- timeout when I tried it...
  refine le_trans (finset.sum_nonneg _) x.2.2,
  exact (λ _ _, finset.sum_nonneg (λ _ _, abs_nonneg _)),
end

lemma coeff_bound [h0r : fact (0 < r)] (F : S → fin (M + 1) → ℤ)
  (hF : ∑ s i, abs ((F s i : ℝ) * r^(i : ℕ)) ≤ c) (n : fin (M + 1)) (s : S) :
  abs (F s n : ℝ) ≤ c / min (r ^ M) 1 :=
begin
  rw le_div_iff (lt_min (pow_pos h0r _) zero_lt_one),
  calc abs ↑(F s n) * min (r ^ M) 1 ≤ abs ↑(F s n) * r ^ n.1 : begin
    refine mul_le_mul_of_nonneg_left _ (abs_nonneg _),
    cases le_or_lt r 1 with hr1 hr1,
    { refine le_trans (min_le_left _ _) _,
      exact pow_le_pow_of_le_one (le_of_lt h0r) hr1 (nat.lt_add_one_iff.1 n.2) },
    { exact le_trans (min_le_right _ _) (one_le_pow_of_one_le (le_of_lt hr1) _) },
  end
  ... = abs ((F s n : ℝ) * r ^ n.1) : by rw [abs_mul, abs_of_pos (pow_pos h0r _)]
  ... ≤ ∑ i, abs ((F s i : ℝ) * r ^ (i : ℕ)) :
    single_le_sum (λ (i : fin (M + 1)) _, abs_nonneg ((F s i : ℝ) * r ^ i.val)) (mem_univ n)
  ... ≤ ∑ s i, abs ((F s i : ℝ) * r^(i : ℕ)) : begin
    refine single_le_sum (λ _ _, _) (mem_univ s),
    exact sum_nonneg (λ _ _, (abs_nonneg _)),
  end
  ... ≤ c : hF
end

private def temp_map [fact (0 < r)] (F : Mbar_bdd r S c M) (n : fin (M + 1)) (s : S) :
  Icc (ceil (-(c / min (r ^ M) 1))) (floor (c / min (r ^ M) 1)) :=
let h := abs_le.1 $ coeff_bound F.1 F.2.2 n s in
⟨F.1 s n, ceil_le.2 $ h.1, le_floor.2 h.2⟩

instance [fact (0 < r)] : fintype (Mbar_bdd r S c M) :=
fintype.of_injective temp_map begin
  rintros ⟨f1, hf1⟩ ⟨f2, hf2⟩ h,
  ext s n,
  change (temp_map ⟨f1, hf1⟩ n s).1 = (temp_map ⟨f2, hf2⟩ n s).1,
  rw h,
end

def ι {M N : ℕ} (h : M ≤ N) : fin M ↪ fin N := (fin.cast_le h).to_embedding

-- Should this be in mathlib?
lemma sum_eq_sum_map_ι {M N : ℕ} (h : M ≤ N) (f : fin N → ℝ) :
  ∑ i, f (ι h i) = ∑ j in finset.map (ι h) finset.univ, f j :=
finset.sum_bij' (λ a _, ι h a) (λ a ha, by {rw mem_map, exact ⟨a, ha, rfl⟩})
(λ a ha, rfl) (λ a ha, ⟨a.1, begin
  rcases finset.mem_map.mp ha with ⟨⟨w,ww⟩,hw,rfl⟩,
  change w < M,
  linarith,
end ⟩)
(λ a ha, finset.mem_univ _) (λ a ha, by tidy) (λ a ha, by tidy)

/-- The transition maps between the Mbar_bdd sets. -/
def transition (r : ℝ) {S : Fintype} {c : ℝ} {M N : ℕ} (h : M ≤ N) :
  Mbar_bdd r S c N → Mbar_bdd r S c M := λ ⟨a,ha⟩,
⟨λ s i, a s (ι (by linarith) i),
begin
  refine ⟨λ s, ha.1 _, le_trans _ ha.2⟩,
  apply finset.sum_le_sum,
  intros s hs,
  let I := finset.map (ι (by linarith : M+1 ≤ N+1))
    (finset.univ : finset (fin (M+1))),
  refine le_trans _
    (finset.sum_le_sum_of_subset_of_nonneg (finset.subset_univ I) _),
  { rw ← sum_eq_sum_map_ι,
    apply le_of_eq,
    congr },
  { intros,
    exact (abs_nonneg _) }
end⟩

lemma transition_eq {r : ℝ} {S : Fintype} {c : ℝ} {M N : ℕ} (h : M ≤ N)
  (F : Mbar_bdd r S c N) (s : S) (i : fin (M+1)) :
  (transition r h F).1 s i = F.1 s (ι (by linarith) i) := by tidy

lemma transition_transition {r : ℝ} {S : Fintype} {c : ℝ}
  {M N K : ℕ} (h : M ≤ N) (hh : N ≤ K) (x : Mbar_bdd r S c K):
  transition r h (transition r hh x) = transition r (le_trans h hh) x := by tidy

@[reducible] def limit (r S c) :=
{ F : Π (M : ℕ), Mbar_bdd r S c M // ∀ (M N : ℕ) (h : M ≤ N), transition r h (F N) = F M }

def emb_aux : limit r S c → (Π (M : ℕ), Mbar_bdd r S c M) := coe

section topological_structure

instance : topological_space (Mbar_bdd r S c M) := ⊥
instance : discrete_topology (Mbar_bdd r S c M) := ⟨rfl⟩

-- sanity check
example : t2_space (Mbar_bdd r S c M) := by apply_instance
example : totally_disconnected_space (Mbar_bdd r S c M) := by apply_instance
example [fact (0 < r)] : compact_space (Mbar_bdd r S c M) := by apply_instance

--TODO: Fill in the sorry to obtain compactness of Mbar_bdd.limit
def emb (r S c) : closed_embedding (@emb_aux r S c) :=
{ induced := rfl,
  inj := by tidy,
  closed_range := begin
    sorry,
  end }

instance [fact (0 < r)] : compact_space (limit r S c) :=
begin
  erw [← compact_iff_compact_space, compact_iff_compact_univ, compact_iff_compact_in_subtype],
  apply is_closed.compact,
  exact embedding_is_closed (emb r S c).to_embedding (emb r S c).closed_range is_closed_univ,
end

end topological_structure


end Mbar_bdd
