import for_mathlib.exact_seq3
import for_mathlib.bicartesian2
.

open category_theory category_theory.limits

universe u
local notation `𝓐` := Ab.{u}

-- Consider the following diagram
variables {     Kv₁   Kv₂        : 𝓐}
variables {Kh₁  A₁₁   A₁₂  Qh₁   : 𝓐}
variables {Kh₂  A₂₁   A₂₂  Qh₂   : 𝓐}
variables {     Qv₁   Qv₂        : 𝓐}
-- with morphisms
variables                         (fKv : Kv₁ ⟶ Kv₂)
variables                 {ιv₁ : Kv₁ ⟶ A₁₁} {ιv₂ : Kv₂ ⟶ A₁₂}
variables         {ιh₁ : Kh₁ ⟶ A₁₁} {f₁ : A₁₁ ⟶ A₁₂} {πh₁ : A₁₂ ⟶ Qh₁}
variables (gKh : Kh₁ ⟶ Kh₂) {g₁ : A₁₁ ⟶ A₂₁} {g₂ : A₁₂ ⟶ A₂₂} (gQh : Qh₁ ⟶ Qh₂)
variables         {ιh₂ : Kh₂ ⟶ A₂₁} {f₂ : A₂₁ ⟶ A₂₂} {πh₂ : A₂₂ ⟶ Qh₂}
variables                 {πv₁ : A₂₁ ⟶ Qv₁}  {πv₂ : A₂₂ ⟶ Qv₂}
variables                         (fQv : Qv₁ ⟶ Qv₂)
-- with exact rows and columns
variables (H₁ : exact_seq 𝓐 [ιh₁, f₁, πh₁])
variables (H₂ : exact_seq 𝓐 [ιh₂, f₂, πh₂])
variables (V₁ : exact_seq 𝓐 [ιv₁, g₁, πv₁])
variables (V₂ : exact_seq 𝓐 [ιv₂, g₂, πv₂])
-- and such that all the extremal maps are appropriately monos or epis
variables [mono ιv₁] [mono ιv₂] [mono ιh₁] [mono ιh₂]
variables [epi πv₁] [epi πv₂] [epi πh₁] [epi πh₂]
-- of course the diagram should commute
variables (sqᵤ : commsq fKv ιv₁ ιv₂ f₁)
variables (sqₗ : commsq ιh₁ gKh g₁ ιh₂) (sqm : commsq f₁ g₁ g₂ f₂)
variables (sqᵣ : commsq πh₁ g₂ gQh πh₂)
variables (sqₛ : commsq f₂ πv₁ πv₂ fQv)

include H₁ H₂ sqₗ sqm sqᵣ

open_locale zero_object
open category_theory.abelian

lemma commsq.bicartesian_iff_isos : sqm.bicartesian ↔ (is_iso gKh ∧ is_iso gQh) :=
begin
  delta commsq.bicartesian,
  split,
  { intro h, split,
    { rw is_iso_iff_mono_and_epi, split,
      { rw [AddCommGroup.mono_iff_ker_eq_bot, eq_bot_iff], sorry },
      { sorry } },
    { sorry } },
  { sorry }
end
