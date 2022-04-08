import for_mathlib.exact_seq3
.

open category_theory category_theory.limits

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

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

include H₁ H₂ V₁ V₂

lemma bicartesian.isos_of_isos (hfKv : is_iso fKv) (hfQv : is_iso fQv) :
  is_iso gKh ∧ is_iso gQh :=
sorry

lemma bicartesian.isos_iff_isos : (is_iso fKv ∧ is_iso fQv) ↔ (is_iso gKh ∧ is_iso gQh) :=
begin
  split; intro h,
  { apply bicartesian.isos_of_isos fKv gKh gQh fQv H₁ H₂ V₁ V₂ h.1 h.2 },
  { apply bicartesian.isos_of_isos gKh fKv fQv gQh V₁ V₂ H₁ H₂ h.1 h.2 }
end
