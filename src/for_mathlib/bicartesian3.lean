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
  split,
  { intro h, split,
    { haveI : mono gKh,
      { refine preadditive.mono_of_cancel_zero _ (λ P g hg, _),
        apply zero_of_comp_mono ιh₁,
        apply pullback_cone.is_limit.hom_ext h.is_limit,
        { rw [pullback_cone.mk_fst, category.assoc, zero_comp, (H₁.extract 0 2).w, comp_zero] },
        { rw [pullback_cone.mk_snd, category.assoc, sqₗ.w, ← category.assoc, hg, zero_comp,
            zero_comp] } },
        obtain ⟨l, hl₁, hl₂ : l ≫ g₁ = _⟩ :=
          pullback_cone.is_limit.lift' h.is_limit 0 ιh₂ (by simp [(H₂.extract 0 2).w]),
        let ker := is_limit_of_exact_of_mono _ _ ((exact_iff_exact_seq _ _).2 (H₁.extract 0 2)),
        obtain ⟨inv, hinv : inv ≫ ιh₁ = l⟩ := kernel_fork.is_limit.lift' ker l hl₁,
        have hinv' : inv ≫ gKh = 𝟙 _,
        { rw [← cancel_mono ιh₂, category.assoc, ← sqₗ.w, reassoc_of hinv, hl₂, category.id_comp] },
        refine ⟨⟨inv, _, hinv'⟩⟩,
        rw [← cancel_mono gKh, category.assoc, hinv', category.comp_id, category.id_comp] },
    { haveI : epi gQh,
      { refine preadditive.epi_of_cancel_zero _ (λ P g hg, _),
        apply zero_of_epi_comp πh₂,
        apply pushout_cocone.is_colimit.hom_ext h.is_colimit,
        { rw [pushout_cocone.mk_inl, ← category.assoc, ← sqᵣ.w, category.assoc, hg, comp_zero,
            comp_zero] },
        { rw [pushout_cocone.mk_inr, ← category.assoc, (H₂.extract 1 2).w, comp_zero, zero_comp] } },
      obtain ⟨l, hl₁ : g₂ ≫ l = _, hl₂⟩ :=
        pushout_cocone.is_colimit.desc' h.is_colimit πh₁ 0 (by simp [(H₁.extract 1 2).w]),
      let coker := is_colimit_of_exact_of_epi _ _ ((exact_iff_exact_seq _ _).2 (H₂.extract 1 2)),
      obtain ⟨inv, hinv : πh₂ ≫ inv = l⟩ := cokernel_cofork.is_colimit.desc' coker l hl₂,
      have hinv' : gQh ≫ inv = 𝟙 _,
      { rw [← cancel_epi πh₁, ← category.assoc, sqᵣ.w, category.assoc, hinv, hl₁, category.comp_id] },
      refine ⟨⟨inv, hinv', _⟩⟩,
      rw [← cancel_epi gQh, reassoc_of hinv', category.comp_id] } },
  { sorry }
end
