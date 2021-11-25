-- import for_mathlib.short_exact_sequence
import laurent_measures.basic
import laurent_measures.theta
import linear_algebra.basic


namespace thm_69

-- open category_theory category_theory.limits
open theta laurent_measures
open_locale nnreal classical big_operators


-- universe u
variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
variables (r : ℝ≥0) [fact (0 < r)] [fact (r < 1)]
-- variables (r : ℝ≥0) [fact ((1 / 2 : ℝ) ^ p.1 = r)]

lemma r_pos : 0 < r ∧ r < 1 := sorry

lemma r_one : r < 1 := sorry

lemma half_ineq : (1 / 2 : ℝ) < r :=
begin
  sorry,
end

noncomputable theory

section ker_theta_half

example (a : ℤ) : ∥ (2 : ℝ) * a ∥ = 2 * ∥ a ∥ :=
begin
  rw normed_field.norm_mul,
  rw real.norm_two,
  field_simp,
  exact int.norm_cast_real a,
  -- simp only [normed_field.norm_mul, mul_eq_mul_left_iff, or_false, bit0_eq_zero, one_ne_zero, real.norm_two],
end

def ϕ : (laurent_measures r (Fintype.of punit)) → (laurent_measures r (Fintype.of punit)) :=
begin
  rintro ⟨f,hF⟩,
  let f₁ : (Fintype.of punit) → ℤ → ℤ := λ s n, 2* f s (n - 1) - f s n,
  use f₁,
  intro s,
  let g₁ : ℤ → ℝ := λ n, ∥ 2 * f s (n - 1) ∥ * r ^ n + ∥ f s n ∥ * r ^ n,
  have Hf_le_g : ∀ b : ℤ, ∥ f₁ s b ∥ * r ^ b ≤ g₁ b,
  { intro b,
    dsimp [f₁, g₁],
    rw ← add_mul,
    have rpow_pos : 0 < (r : ℝ) ^ b := by { apply zpow_pos_of_pos, rw nnreal.coe_pos,
      exact fact.out _ },
    apply (mul_le_mul_right rpow_pos).mpr,
    exact norm_sub_le (2 * f s (b - 1)) (f s b) },
  apply summable_of_nonneg_of_le _ Hf_le_g,
  { apply summable.add,
    have : ∀ b : ℤ, ∥ f s (b - 1) ∥ * r ^ b = r * ∥ f s (b - 1) ∥ * r ^ (b - 1),
    { intro b,
      nth_rewrite_rhs 0 mul_assoc,
      nth_rewrite_rhs 0 mul_comm,
      nth_rewrite_rhs 0 mul_assoc,
      rw [← zpow_add_one₀, sub_add_cancel b 1],
      rw [ne.def, nnreal.coe_eq_zero],
      apply ne_of_gt,
      exact fact.out _ },
    simp_rw [← int.norm_cast_real, int.cast_mul, normed_field.norm_mul, int.norm_cast_real,
      mul_assoc],
    apply @summable.mul_left ℝ _ _ _ _ (λ (b : ℤ), ∥f s (b - 1) ∥ * ↑r ^ b ) (∥ (2 : ℤ) ∥),
    simp_rw [this, mul_assoc],
    apply @summable.mul_left ℝ _ _ _ _ (λ (b : ℤ), ∥f s (b - 1)∥ * ↑r ^ (b - 1)) r,
    have h_comp : (λ (b : ℤ), ∥f s (b - 1)∥ * ↑r ^ (b - 1)) =
      (λ (b : ℤ), ∥f s b∥ * ↑r ^ b) ∘ (λ n, n - 1) := rfl,
    rw h_comp,
    apply summable.comp_injective _ sub_left_injective,
    repeat {apply_instance},
    repeat {specialize hF s, exact hF}, },
  { intro b,
    apply mul_nonneg,
    apply norm_nonneg,
    rw ← nnreal.coe_zpow,
    exact (r ^ b).2 },
end

def θₗ : (laurent_measures r (Fintype.of punit)) →ₗ[ℤ] ℝ :=
{ to_fun := λ F, tsum (λ n, (F punit.star n) * (1 / 2 : ℝ) ^ n),
  map_add' :=
   begin
    intros F G,
    rw ← tsum_add,
    apply tsum_congr,
    intro m,
    rw [← add_mul, mul_eq_mul_right_iff],
    apply or.intro_left,
    rw [← int.cast_add, int.cast_inj],
    apply laurent_measures.add_apply,
    sorry, sorry,
  end,
  map_smul' := sorry }

--for MATHLIB?
variables [α : Type*] [add_group α] [topological_space α] [has_continuous_add α] [has_sub α]

-- lemma has_sum.int_even_add_odd {f : ℤ → α} {a b : α} (he : has_sum (λ k, f (2 * k)) a)
--   (ho : has_sum (λ k, f (2 * k + 1)) b) :
--   has_sum f (a + b) :=
-- begin
--   have := mul_right_injective₀ (@two_ne_zero ℤ _ _),
--   replace he := this.has_sum_range_iff.2 he,
--   replace ho := ((add_left_injective 1).comp this).has_sum_range_iff.2 ho,
--   refine he.add_is_compl _ ho,
--   simpa [(∘)] using int.is_compl_even_odd,
-- end
--

lemma θ_ϕ_complex (F : laurent_measures r (Fintype.of punit)) : (θₗ r ∘ ϕ r) F = 0 :=
begin
  rcases F with ⟨f, hf⟩,
  convert_to ∑' (n : ℤ), ((2 * f punit.star (n - 1) - f punit.star n) : ℝ) * (1 / 2) ^ n = 0,
  { apply tsum_congr,
    intro b,
    rw ← inv_eq_one_div,
    apply (mul_left_inj' (@zpow_ne_zero ℝ _ _ b (inv_ne_zero two_ne_zero))).mpr,
    have : (2 : ℝ) * (f punit.star (b - 1)) = ((2 : ℤ) * (f punit.star (b -1))) := by {rw [← int.cast_one, int.cast_bit0] },
    rw [this, ← int.cast_mul, ← int.cast_sub],
    refl },
  have h_neg : summable (λ n, ((f punit.star n) : ℝ) * (1 / 2) ^ n),
  { specialize hf punit.star,
    apply summable_of_summable_norm,
    --`[FAE]` if the sum were over ℕ, life would be easy
    sorry},
  have h_pos : has_sum (λ n, ((2 * f punit.star (n - 1)) : ℝ) * (1 / 2) ^ n) h_neg.some,
  { have div_half : ∀ b : ℤ, (1 / 2 : ℝ) ^ b * (2 : ℝ) = (1 / 2) ^ ( b - 1),
    { intro b,
      rw [← inv_eq_one_div, @zpow_sub_one₀ ℝ _ _ (inv_ne_zero two_ne_zero) b],
      apply (mul_right_inj' (@zpow_ne_zero ℝ _ _ b (inv_ne_zero two_ne_zero))).mpr,
      exact (inv_inv₀ 2).symm },
    have h_comp : (λ (b : ℤ), ((f punit.star (b - 1)) : ℝ ) * (1 / 2) ^ (b - 1)) =
      (λ (b : ℤ), ((f punit.star b) : ℝ) * (1 / 2) ^ b) ∘ (λ n, n - 1) := rfl,
    simp_rw [mul_comm, ← mul_assoc, div_half, mul_comm, h_comp],
    let e : ℤ ≃ ℤ := ⟨λ n : ℤ, n - 1, λ n, n + 1, by {intro, simp}, by {intro, simp}⟩,
    apply (equiv.has_sum_iff e).mpr,
    exact h_neg.some_spec },
  simp_rw [sub_mul, tsum_sub h_pos.summable h_neg, sub_eq_zero],
  --'[FAE]' It should now just be a matter of combining h_neg with h_pos (which says that the two sums coincide, so their difference is 0)
  -- have foo := h_pos.tsum_eq,
  -- have boo := h_neg.has_sum.tsum_eq,
  -- have too := h_pos.unique foo,
  -- rw foo,

  -- apply boo.unique,
  -- apply tsum.eq,
  -- exact boo,

  -- have := tsum_sub h_pos h_neg,
  -- rw this,
  -- simp_rw ← sub_mul at this,
  -- apply tsum_sub (λ s n, 2 * f s (n - 1)) (λ s n, f s n),
  -- simp [pi.has_sub],
  sorry,

end


lemma θ_ϕ_exact (F : laurent_measures r (Fintype.of punit)) (hF : θₗ r F = 0) :
  ∃ G, ϕ r G = F := sorry


end ker_theta_half

section SES_thm69

local notation `ℳ` := real_measures

variable (S : Fintype)
-- variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] [fact ((1/2 : ℝ) ^ (p : ℝ) = r)]

include r

/-- This `θ₂` is the "measurification" of the map `θₗ` of
Theorem 6.9. Thus, `to_meas_θ` is the map inducing the isomorphism of Theorem 6.9 (2)-/
def θ₂ : laurent_measures r S → ℳ p S :=
λ F s, θₗ r ⟨(λ _, F s), (λ _, F.2 s)⟩

lemma θ₂_zero :
 (θ₂ p r S (0 : laurent_measures r S)) = 0 := sorry

lemma θ₂_add (F G : laurent_measures r S) :
 (θ₂ p r S (F + G)) = (θ₂ p r S F) + (θ₂ p r S G) := sorry

/--This `lemma to_meas_θ_bound` is precisely Prop 7.2 (3) of `Analytic.pdf`-/
lemma θ₂_bound : ∃ (C : ℝ≥0), ∀ (c : ℝ≥0) (F : laurent_measures r S),
  ∥ F ∥ ≤ c → ∥ θ₂ p r S F ∥₊ ≤ C * c := sorry

def to_add_hom_θ₂ : add_hom (laurent_measures r S) (ℳ p S) :=
add_monoid_hom.mk' (λ F, θ₂ p r S F)
begin
    intros a b,
    have := θ₂_add p r S a b,
    exact this,
  end

def Θ : comphaus_filtered_pseudo_normed_group_hom (laurent_measures r S) (ℳ p S) :=
  { to_fun := θ₂ p r S,
    bound' := θ₂_bound p r S,
    continuous' := sorry, -- [FAE] I guess that this is Prop 7.2 (4) of `Analytic.pdf`
    -- .. to_add_hom_meas_θ ξ r S p,
    map_add' := (to_add_hom_θ₂ p r S).2,
    map_zero' := sorry }


-- lemma chain_complex_thm69 (F : laurent_measures r S) : Θ p r S (𝑓 • F) = 0 :=
-- begin
--   funext s,
--   sorry,
--   -- simp only [real_measures.zero_apply],
--   -- dsimp [Θ],
--   -- dsimp [to_meas_θ],
--   -- dsimp [θ],
--   -- dsimp [has_scalar],
--   -- rw pi.has_scalar,
-- end


/-
From here onwards, the bundled version
-/
-- variable [imCHFPNG : has_images (CompHausFiltPseuNormGrp.{u})]
-- variable [zerCHFPNG : has_zero_morphisms (CompHausFiltPseuNormGrp.{u})]
-- variable [kerCHFPNG : has_kernels (CompHausFiltPseuNormGrp.{u})]



-- def SES_thm69 (S : Fintype) : @category_theory.short_exact_sequence CompHausFiltPseuNormGrp.{u} _
--   imCHFPNG zerCHFPNG kerCHFPNG :=
-- { fst := bundled.of (laurent_measures r S),
--   snd := bundled.of (laurent_measures r S),
--   trd := bundled.of (ℳ p S),
--   f :=
--   begin
--     let φ := λ (F : laurent_measures r S), (ker_θ₂_generator r) • F,
--     use φ,
--     sorry,
--     sorry,
--     sorry,
--     sorry,-- [FAE] These four are the properties that the scalar multiplication by a measure on the
--     --singleton (as endomorphism of S-measures) must satisfy
--   end,
--   g := @Θ r _ S p _ _ _,
--   mono' := sorry,
--   epi' := sorry,
--   exact' := sorry }

end SES_thm69

end thm_69
