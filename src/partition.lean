import data.real.nnreal
import topology.algebra.infinite_sum
import topology.instances.ennreal
import topology.algebra.monoid

open_locale nnreal big_operators
open finset

def mask_fun {α : Type*} (f : α → ℝ≥0) (mask : α → Prop) [∀ n, decidable (mask n)] : α → ℝ≥0 :=
λ n, if mask n then f n else 0

structure recursion_data (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (k : ℕ) :=
(m : fin N → Prop)
(dec_inst : ∀ i, decidable (m i))
(hm :  ∃! i, m i)
(partial_sums : fin N → ℝ≥0)
(h₁ : ∑ i, partial_sums i = ∑ n in range (k + 1), f n)
(h₂ : ∀ i, partial_sums i ≤ (∑ n in range (k + 1), f n) / N + 1)

def recursion_data_zero (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
  recursion_data N hN f hf 0 :=
{ m := λ j, j = ⟨0, hN⟩,
  dec_inst := by apply_instance,
  hm := ⟨_, rfl, by simp⟩,
  partial_sums := λ j, if j = ⟨0, hN⟩ then f 0 else 0,
  h₁ := by simp,
  h₂ :=
  begin
    intros i,
    split_ifs,
    { simp,
      refine (hf 0).trans _,
      exact self_le_add_left 1 (f 0 / ↑N) },
    { simp }
  end }

noncomputable def recursion_data_succ (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (k : ℕ)
  (dat : recursion_data N hN f hf k) :
  recursion_data N hN f hf (k + 1) :=
let I := (finset.univ : finset (fin N)).exists_min_image
  dat.partial_sums ⟨⟨0, hN⟩, finset.mem_univ _⟩ in
{ m := λ j, j = I.some,
  dec_inst := by apply_instance,
  hm := ⟨I.some, by simp, by simp⟩,
  partial_sums := λ i, dat.partial_sums i + (if i = I.some then f (k + 1) else 0),
  h₁ := begin
    rw sum_range_succ _ (k + 1),
    simp [finset.sum_add_distrib, dat.h₁, add_comm],
  end,
  h₂ := begin
    intros i,
    split_ifs,
    { rw h,
      have : dat.partial_sums I.some * N ≤ (∑ n in range (k + 1 + 1), f n),
      { calc dat.partial_sums I.some * N
            = ∑ i : fin N, dat.partial_sums I.some : _
        ... ≤ ∑ i, dat.partial_sums i : _ -- follows from I
        ... = ∑ n in range (k + 1), f n : dat.h₁
        ... ≤ ∑ n in range (k + 1 + 1), f n : _,
        { simp only [finset.sum_const, finset.card_fin, nsmul_eq_mul, mul_comm] },
        { obtain ⟨-, HI⟩ := I.some_spec,
          apply finset.sum_le_sum,
          intros j hj, exact HI j hj },
        { rw sum_range_succ _ (k + 1),
          simp } },
      have : dat.partial_sums I.some ≤ (∑ n in range (k + 1 + 1), f n) / ↑N,
      { rwa nnreal.le_div_iff_mul_le, exact_mod_cast hN.ne' },
      exact add_le_add this (hf (k + 1)) },
    { calc dat.partial_sums i + 0
          ≤ (∑ n in range (k + 1), f n) / ↑N + 1 : by simpa using dat.h₂ i
      ... ≤ (∑ n in range (k + 1 + 1), f n) / ↑N + 1 : add_le_add _ le_rfl,
      simp only [div_eq_mul_inv, fin.sum_univ_eq_sum_range],
      refine mul_le_mul' _ le_rfl,
      simp only [finset.sum_range_succ],
      exact self_le_add_left _ _ }
  end }

noncomputable def partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
  Π i : ℕ, (recursion_data N hN f hf i)
| 0 := recursion_data_zero N hN f hf
| (k + 1) := recursion_data_succ N hN f hf k (partition k)

lemma partition_sums_aux (k : ℕ) (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1)
  (i : fin N) :
  (partition N hN f hf (k + 1)).partial_sums i
  = (partition N hN f hf k).partial_sums i
  + (@ite _ ((partition N hN f hf (k + 1)).m i) ((partition N hN f hf (k + 1)).dec_inst i) (f (k + 1)) 0) :=
by simp [partition, recursion_data_succ]

lemma partition_sums (k : ℕ) (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1)
  (i : fin N) :
  (partition N hN f hf k).partial_sums i
  = ∑ n in range (k + 1), @mask_fun _ f (λ k, (partition N hN f hf k).m i)
    (λ k, (partition N hN f hf k).dec_inst i) n :=
begin
  induction k with k IH,
  { dsimp [partition, mask_fun], simp, dsimp [partition, recursion_data_zero], congr },
  rw [partition_sums_aux, IH, sum_range_succ _ k.succ, add_comm],
  congr' 1
end

lemma exists_partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (hf' : summable f) :
  ∃ (mask : fin N → ℕ → Prop) [∀ i n, decidable (mask i n)], by exactI
    (∀ n, ∃! i, mask i n) ∧ (∀ i, ∑' n, mask_fun f (mask i) n ≤ (∑' n, f n) / N + 1) :=
begin
  let mask : fin N → ℕ → Prop := λ i, λ n, (partition N hN f hf n).m i,
  let partial_sums : fin N → ℕ → ℝ≥0 := λ i, λ n, (partition N hN f hf n).partial_sums i,
  haveI : ∀ i n, decidable (mask i n) := λ i, λ n, (partition N hN f hf n).dec_inst i,
  have h_sum : ∀ k, ∀ i, ∑ n in range k, mask_fun f (mask i) n ≤ (∑ n in range k, f n) / ↑N + 1,
  { intros k i,
    cases k,
    { simp [mask_fun, mask] },
    convert (partition N hN f hf k).h₂ i,
    convert (partition_sums k N hN f hf i).symm using 1,
    ext n m,
    simp [mask, mask_fun],
    congr,
    ext i,
    split_ifs,
    simp },
  refine ⟨mask, by apply_instance, _, _⟩,
  { intros n,
    exact (partition N hN f hf n).hm },
  { intros i,
    set S₁ : ℝ≥0 := ∑' (n : ℕ), f n,
    have hf'' : has_sum f S₁ := hf'.has_sum,
    have hf''' : has_sum _ (S₁ / N) := hf''.mul_right (N:ℝ≥0)⁻¹,
    have : mask_fun f (mask i) ≤ f,
    { intros n,
      dsimp [mask_fun],
      split_ifs,
      { refl },
      { exact (f n).2 } },
    obtain ⟨S₂, -, h_mask⟩ := nnreal.exists_le_has_sum_of_le this hf'',
    rw h_mask.tsum_eq,
    rw nnreal.has_sum_iff_tendsto_nat at hf''' h_mask,
    have := filter.tendsto.add_const 1 hf''',
    apply le_of_tendsto_of_tendsto' h_mask this,
    intros n,
    simp only [div_eq_mul_inv, finset.sum_mul] at h_sum ⊢,
    exact h_sum n i }
end
