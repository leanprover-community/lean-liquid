import for_mathlib.short_exact_sequence
import laurent_measures.basic
import laurent_measures.theta


namespace thm_69

open category_theory category_theory.limits theta laurent_measures
open_locale nnreal classical big_operators


universe u
-- variable (ξ : ℝ)
variables (r : ℝ≥0) [fact (0 < r)]

noncomputable theory

instance (S : Fintype) : has_scalar (laurent_measures r (Fintype.of punit)) (laurent_measures r S) :=
{ smul := sorry}

section SES_thm69

local notation `ℳ` := real_measures
local notation `𝑓` := (ker_θ₂_generator r)
variable (S : Fintype)
variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] [fact ((1/2 : ℝ) ^ (p : ℝ) = r)]

include r

/-- This `θ₂` is the "measurification" of the map `θ₂.to_linear` of
Theorem 6.9. Thus, `to_meas_θ` is the map inducing the isomorphism of Theorem 6.9 (2)-/
def θ₂ : laurent_measures r S → ℳ p S :=
λ F s, θ₂.to_linear r ⟨(λ _, F s), (λ _, F.2 s)⟩

lemma θ₂_zero :
 (θ₂ r S p (0 : laurent_measures r S)) = 0 := sorry

lemma θ₂_add (F G : laurent_measures r S) :
 (θ₂ r S p (F + G)) = (θ₂ r S p F) + (θ₂ r S p G) := sorry

/--This `lemma to_meas_θ_bound` is precisely Prop 7.2 (3) of `Analytic.pdf`-/
lemma θ₂_bound : ∃ (C : ℝ≥0), ∀ (c : ℝ≥0) (F : laurent_measures r S),
  ∥ F ∥ ≤ c → ∥ θ₂ r S p F ∥₊ ≤ C * c := sorry

def to_add_hom_θ₂ : add_hom (laurent_measures r S) (ℳ p S) :=
add_monoid_hom.mk' (λ F, θ₂ r S p F)
begin
    intros a b,
    have := θ₂_add r S p a b,
    exact this,
  end

def Θ : comphaus_filtered_pseudo_normed_group_hom (laurent_measures r S) (ℳ p S) :=
  { to_fun := θ₂ r S p,
    bound' := θ₂_bound r S p,
    continuous' := sorry, -- [FAE] I guess that this is Prop 7.2 (4) of `Analytic.pdf`
    -- .. to_add_hom_meas_θ ξ r S p,
    map_add' := (to_add_hom_θ₂ r S p).2,
    map_zero' := sorry }


lemma chain_complex_thm69 (F : laurent_measures r S) : Θ r S p (𝑓 • F) = 0 :=
begin
  funext s,
  sorry,
  -- simp only [real_measures.zero_apply],
  -- dsimp [Θ],
  -- dsimp [to_meas_θ],
  -- dsimp [θ],
  -- dsimp [has_scalar],
  -- rw pi.has_scalar,
end


/-
From here onwards, the bundled version
-/
variable [imCHFPNG : has_images (CompHausFiltPseuNormGrp.{u})]
variable [zerCHFPNG : has_zero_morphisms (CompHausFiltPseuNormGrp.{u})]
variable [kerCHFPNG : has_kernels (CompHausFiltPseuNormGrp.{u})]



def SES_thm69 (S : Fintype) : @category_theory.short_exact_sequence CompHausFiltPseuNormGrp.{u} _
  imCHFPNG zerCHFPNG kerCHFPNG :=
{ fst := bundled.of (laurent_measures r S),
  snd := bundled.of (laurent_measures r S),
  trd := bundled.of (ℳ p S),
  f :=
  begin
    let φ := λ (F : laurent_measures r S), (ker_θ₂_generator r) • F,
    use φ,
    sorry,
    sorry,
    sorry,
    sorry,-- [FAE] These four are the properties that the scalar multiplication by a measure on the
    --singleton (as endomorphism of S-measures) must satisfy
  end,
  g := @Θ r _ S p _ _ _,
  mono' := sorry,
  epi' := sorry,
  exact' := sorry }

end SES_thm69

end thm_69
