-- import for_mathlib.exact_seq3
-- import for_mathlib.salamander
-- .

-- open category_theory category_theory.limits

-- variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

-- -- Consider the following diagram
-- variables {     Kv₁   Kv₂        : 𝓐}
-- variables {Kh₁  A₁₁   A₁₂  Qh₁   : 𝓐}
-- variables {Kh₂  A₂₁   A₂₂  Qh₂   : 𝓐}
-- variables {     Qv₁   Qv₂        : 𝓐}
-- -- with morphisms
-- variables                         (fKv : Kv₁ ⟶ Kv₂)
-- variables                 {ιv₁ : Kv₁ ⟶ A₁₁} {ιv₂ : Kv₂ ⟶ A₁₂}
-- variables         {ιh₁ : Kh₁ ⟶ A₁₁} {f₁ : A₁₁ ⟶ A₁₂} {πh₁ : A₁₂ ⟶ Qh₁}
-- variables (gKh : Kh₁ ⟶ Kh₂) {g₁ : A₁₁ ⟶ A₂₁} {g₂ : A₁₂ ⟶ A₂₂} (gQh : Qh₁ ⟶ Qh₂)
-- variables         {ιh₂ : Kh₂ ⟶ A₂₁} {f₂ : A₂₁ ⟶ A₂₂} {πh₂ : A₂₂ ⟶ Qh₂}
-- variables                 {πv₁ : A₂₁ ⟶ Qv₁}  {πv₂ : A₂₂ ⟶ Qv₂}
-- variables                         (fQv : Qv₁ ⟶ Qv₂)
-- -- with exact rows and columns
-- variables (H₁ : exact_seq 𝓐 [ιh₁, f₁, πh₁])
-- variables (H₂ : exact_seq 𝓐 [ιh₂, f₂, πh₂])
-- variables (V₁ : exact_seq 𝓐 [ιv₁, g₁, πv₁])
-- variables (V₂ : exact_seq 𝓐 [ιv₂, g₂, πv₂])
-- -- and such that all the extremal maps are appropriately monos or epis
-- variables [mono ιv₁] [mono ιv₂] [mono ιh₁] [mono ιh₂]
-- variables [epi πv₁] [epi πv₂] [epi πh₁] [epi πh₂]
-- -- of course the diagram should commute
-- variables (sqᵤ : fKv ≫ ιv₂ = ιv₁ ≫ f₁)
-- variables (sqₗ : ιh₁ ≫ g₁ = gKh ≫ ιh₂) (sqm : f₁ ≫ g₂ = g₁ ≫ f₂)
-- variables (sqᵣ : πh₁ ≫ gQh = g₂ ≫ πh₂)
-- variables (sqₛ : f₂ ≫ πv₂ = πv₁ ≫ fQv)

-- include H₁ H₂ V₁ V₂ sqᵤ sqₗ sqm sqᵣ sqₛ

-- open_locale zero_object
-- open category_theory.abelian

-- lemma bicartesian.isos_of_isos (hfKv : is_iso fKv) (hfQv : is_iso fQv) :
--   is_iso gKh ∧ is_iso gQh :=
-- begin
--   resetI,
--   have mgKh : mono gKh,
--   { have sq : (0 : 0 ⟶ Kv₁) ≫ ιv₁ = 0 ≫ ιh₁ := (is_zero_zero _).eq_of_src _ _,
--     rw (tfae_mono 0 gKh).out 0 2,
--     apply (LBC.three_x_three_left_col _ H₁.pair H₂.pair V₁.pair V₂.pair
--       sq sqᵤ sqₗ sqm).1,
--     apply exact_zero_left_of_mono, },
--   have egKh : epi gKh,
--   { exact LBC.four_lemma_left_epi V₁ V₂ H₁.pair H₂.pair sqᵤ sqₗ sqm sqₛ, },
--   have mgQh : mono gQh,
--   { exact LBC.four_lemma_right_mono V₁ V₂ (H₁.drop 1).pair (H₂.drop 1).pair sqᵤ sqm sqᵣ sqₛ, },
--   have egQh : epi gQh,
--   { have sq : πh₂ ≫ (0 : _ ⟶ 0) = πv₂ ≫ 0 := (is_zero_zero _).eq_of_tgt _ _,
--     rw (tfae_epi 0 gQh).out 0 2,
--     apply (LBC.three_x_three_right_col
--       (H₁.drop 1).pair (H₂.drop 1).pair _ (V₁.drop 1).pair (V₂.drop 1).pair
--       sqm sqᵣ sqₛ sq).1,
--     rw ← epi_iff_exact_zero_right, apply_instance },
--   exactI ⟨is_iso_of_mono_of_epi _, is_iso_of_mono_of_epi _⟩
-- end

-- lemma bicartesian.isos_iff_isos : (is_iso fKv ∧ is_iso fQv) ↔ (is_iso gKh ∧ is_iso gQh) :=
-- begin
--   split; intro h,
--   { apply bicartesian.isos_of_isos fKv gKh gQh fQv H₁ H₂ V₁ V₂ _ _ _ _ _ h.1 h.2,
--     assumption' },
--   { apply bicartesian.isos_of_isos gKh fKv fQv gQh V₁ V₂ H₁ H₂ _ _ _ _ _ h.1 h.2;
--     symmetry, assumption' }
-- end
