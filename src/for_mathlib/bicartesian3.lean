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

open_locale zero_object
open category_theory.abelian

def is_limit_of_is_limit_comp {X Y Z : 𝓐} {f : X ⟶ Y} {g : Y ⟶ Z}
  {c : kernel_fork (f ≫ g)} (hc : is_limit c) (h : c.ι ≫ f = 0) :
  is_limit (kernel_fork.of_ι c.ι h) :=
is_limit.of_ι _ _
  (λ T l hl, hc.lift (kernel_fork.of_ι l (by rw [reassoc_of hl, zero_comp])))
  (λ T l hl, hc.fac _ _)
  (λ T l hl m hm, fork.is_limit.hom_ext hc (by { erw [hm, hc.fac], refl }))

def is_colimit_of_is_colimit_comp {X Y Z : 𝓐} {f : X ⟶ Y} {g : Y ⟶ Z}
  {c : cokernel_cofork (f ≫ g)} (hc : is_colimit c) (h : g ≫ c.π = 0) :
  is_colimit (cokernel_cofork.of_π c.π h) :=
is_colimit.of_π _ _
  (λ T l hl, hc.desc (cokernel_cofork.of_π l (by rw [category.assoc, hl, comp_zero])))
  (λ T l hl, hc.fac _ _)
  (λ T l hl m hm, cofork.is_colimit.hom_ext hc (by { erw [hm, hc.fac], refl }))

section
include sqₗ sqm

lemma is_iso_of_is_limit (H₁ : exact ιh₁ f₁) (H₂ : exact ιh₂ f₂)
  (h : is_limit (pullback_cone.mk f₁ g₁ sqm.w)) : is_iso gKh :=
begin
  haveI : mono gKh,
  { refine preadditive.mono_of_cancel_zero _ (λ P g hg, _),
    apply zero_of_comp_mono ιh₁,
    apply pullback_cone.is_limit.hom_ext h,
    { rw [pullback_cone.mk_fst, category.assoc, zero_comp, H₁.w, comp_zero] },
    { rw [pullback_cone.mk_snd, category.assoc, sqₗ.w, ← category.assoc, hg, zero_comp,
        zero_comp] } },
  obtain ⟨l, hl₁, hl₂ : l ≫ g₁ = _⟩ :=
    pullback_cone.is_limit.lift' h 0 ιh₂ (by simp [H₂.w]),
  let ker := is_limit_of_exact_of_mono _ _ H₁,
  obtain ⟨inv, hinv : inv ≫ ιh₁ = l⟩ := kernel_fork.is_limit.lift' ker l hl₁,
  have hinv' : inv ≫ gKh = 𝟙 _,
   { rw [← cancel_mono ιh₂, category.assoc, ← sqₗ.w, reassoc_of hinv, hl₂, category.id_comp] },
  refine ⟨⟨inv, _, hinv'⟩⟩,
  rw [← cancel_mono gKh, category.assoc, hinv', category.comp_id, category.id_comp]
end

end

section
include sqm sqᵣ

lemma is_iso_of_is_colimit (H₁ : exact f₁ πh₁) (H₂ : exact f₂ πh₂)
  (h : is_colimit (pushout_cocone.mk _ _ sqm.w)) : is_iso gQh :=
begin
  haveI : epi gQh,
  { refine preadditive.epi_of_cancel_zero _ (λ P g hg, _),
    apply zero_of_epi_comp πh₂,
    apply pushout_cocone.is_colimit.hom_ext h,
    { rw [pushout_cocone.mk_inl, ← category.assoc, ← sqᵣ.w, category.assoc, hg, comp_zero,
        comp_zero] },
    { rw [pushout_cocone.mk_inr, ← category.assoc, H₂.w, comp_zero, zero_comp] } },
  obtain ⟨l, hl₁ : g₂ ≫ l = _, hl₂⟩ :=
    pushout_cocone.is_colimit.desc' h πh₁ 0 (by simp [H₁.w]),
  let coker := is_colimit_of_exact_of_epi _ _ H₂,
  obtain ⟨inv, hinv : πh₂ ≫ inv = l⟩ := cokernel_cofork.is_colimit.desc' coker l hl₂,
  have hinv' : gQh ≫ inv = 𝟙 _,
  { rw [← cancel_epi πh₁, ← category.assoc, sqᵣ.w, category.assoc, hinv, hl₁, category.comp_id] },
  refine ⟨⟨inv, hinv', _⟩⟩,
  rw [← cancel_epi gQh, reassoc_of hinv', category.comp_id]
end

end

include H₁ H₂ sqₗ sqm sqᵣ

lemma commsq.bicartesian_iff_isos : sqm.bicartesian ↔ (is_iso gKh ∧ is_iso gQh) :=
begin
  split,
  { intro h, split,
    { exact is_iso_of_is_limit gKh sqₗ sqm ((exact_iff_exact_seq _ _).2 (H₁.extract 0 2))
      ((exact_iff_exact_seq _ _).2 (H₂.extract 0 2)) h.is_limit },
    { exact is_iso_of_is_colimit gQh sqm sqᵣ ((exact_iff_exact_seq _ _).2 (H₁.extract 1 2))
      ((exact_iff_exact_seq _ _).2 (H₂.extract 1 2)) h.is_colimit } },
  { rintros ⟨gKh_iso, gQh_iso⟩,
    resetI,
    apply commsq.bicartesian.of_is_limit_of_is_colimt,
    { apply is_limit.of_point_iso (limit.is_limit _),
      { apply_instance },
      { let r := pullback.lift _ _ sqm.w,
        let x : Kh₁ ⟶ kernel (pullback.fst : pullback g₂ f₂ ⟶ A₁₂),
        { refine kernel.lift _ (ιh₁ ≫ r) _,
          simp only [(H₁.extract 0 2).w, category.assoc, pullback.lift_fst] },
        haveI : is_iso x,
        { let psq := commsq.of_eq (@pullback.condition _ _ _ _ _ g₂ f₂ _),
          let hker := abelian.is_limit_of_exact_of_mono _ _
            ((exact_iff_exact_seq _ _).2 (H₂.extract 0 2)),
          obtain ⟨u : _ ⟶ Kh₂, hu⟩ := kernel_fork.is_limit.lift' hker
            (kernel.ι (pullback.fst : pullback g₂ f₂ ⟶ A₁₂) ≫ pullback.snd) _,
          { rw fork.ι_of_ι at hu,
            let lsq := commsq.of_eq hu.symm,
            haveI : is_iso u := is_iso_of_is_limit u lsq psq _ _ _,
            { have hxu : x ≫ u = gKh,
              { simp only [← cancel_mono ιh₂, category.assoc, hu, x, kernel.lift_ι_assoc, r,
                pullback.lift_snd, sqₗ.w] },
              have hx : x = gKh ≫ inv u,
              { rw [← is_iso.comp_inv_eq, is_iso.inv_inv, hxu] },
              rw hx,
              apply_instance },
            { exact exact_kernel_ι },
            { exact ((exact_iff_exact_seq _ _).2 (H₂.extract 0 2)) },
            { exact pullback_is_pullback _ _ } },
          { rw [category.assoc, ← pullback.condition, kernel.condition_assoc, zero_comp] } },
        refine @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _ 0 _ _ _ 0 _ _ _
         0 ιh₁ f₁ 0 (kernel.ι (pullback.fst : pullback g₂ f₂ ⟶ A₁₂)) pullback.fst 0 x r (𝟙 _)
         _ _ _ _ _ πh₁ πh₁ (𝟙 _) _ _ _ _ _ _ _ _ _ _ _,
        { simp only [eq_iff_true_of_subsingleton] },
        { simp only [kernel.lift_ι] },
        { simp only [pullback.lift_fst, category.comp_id] },
        { simp only [category.id_comp, category.comp_id] },
        { exact exact_zero_mono ιh₁ },
        { exact (exact_iff_exact_seq _ _).2 (H₁.extract 0 2) },
        { exact (exact_iff_exact_seq _ _).2 (H₁.extract 1 2) },
        { exact exact_zero_mono (kernel.ι pullback.fst) },
        { exact exact_kernel_ι },
        { have : (pullback.fst : pullback g₂ f₂ ⟶ A₁₂) ≫ πh₁ = 0,
          { apply zero_of_comp_mono gQh,
            rw [category.assoc, sqᵣ.w, pullback.condition_assoc, (H₂.extract 1 2).w, comp_zero] },
          apply abelian.exact_of_is_cokernel _ _ this,
          have hex := (exact_iff_exact_seq _ _).2 (H₁.extract 1 2),
          rw ← pullback.lift_fst _ _ sqm.w at hex,
          exact is_colimit_of_is_colimit_comp (abelian.is_colimit_of_exact_of_epi _ _ hex) _ } } },
    { apply is_colimit.of_point_iso (colimit.is_colimit _),
      { apply_instance },
      { let r := pushout.desc _ _ sqm.w,
        let x : cokernel (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) ⟶ Qh₂,
        { refine cokernel.desc _ (r ≫ πh₂) _,
          simp only [(H₂.extract 1 2).w, ← category.assoc, pushout.inr_desc] },
        haveI : is_iso x,
        { let psq := commsq.of_eq (@pushout.condition _ _ _ _ _ f₁ g₁ _),
          let hcoker := abelian.is_colimit_of_exact_of_epi _ _
            ((exact_iff_exact_seq _ _).2 (H₁.extract 1 2)),
          obtain ⟨u : Qh₁ ⟶ _, hu⟩ := cokernel_cofork.is_colimit.desc' hcoker
            (pushout.inl ≫ (cokernel.π (pushout.inr : A₂₁ ⟶ pushout f₁ g₁))) _,
          { rw cofork.π_of_π at hu,
            let lsq := commsq.of_eq hu,
            haveI : is_iso u := is_iso_of_is_colimit u psq lsq _ _ _,
            { have hxu : u ≫ x = gQh,
              { simp only [← cancel_epi πh₁, hu, x, cokernel.π_desc, reassoc_of hu, r,
                  pushout.inl_desc_assoc, sqᵣ.w] },
              have hx : x = inv u ≫ gQh,
              { rw [← is_iso.inv_comp_eq, is_iso.inv_inv, hxu] },
              rw hx,
              apply_instance },
            { exact ((exact_iff_exact_seq _ _).2 (H₁.extract 1 2)) },
            { exact exact_cokernel pushout.inr },
            { exact pushout_is_pushout _ _ } },
          { rw [← category.assoc, pushout.condition, category.assoc, cokernel.condition,
              comp_zero] } },
        refine @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _ _ _ _ _ _ _ _ _
          ιh₂ (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) (cokernel.π (pushout.inr : A₂₁ ⟶ pushout f₁ g₁))
          ιh₂ f₂ πh₂ (𝟙 _) (𝟙 _) r x _ _ _ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _,
        { simp only [category.id_comp, category.comp_id] },
        { simp only [category.id_comp, pushout.inr_desc] },
        { simp only [cokernel.π_desc] },
        { simp only [eq_iff_true_of_subsingleton] },
        { have : ιh₂ ≫ (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) = 0,
          { apply zero_of_epi_comp gKh,
            rw [← sqₗ.w_assoc, ← pushout.condition, reassoc_of (H₁.extract 0 2).w, zero_comp] },
          apply abelian.exact_of_is_kernel _ _ this,
          have hex := (exact_iff_exact_seq _ _).2 (H₂.extract 0 2),
          rw ← pushout.inr_desc _ _ sqm.w at hex,
          exact is_limit_of_is_limit_comp (abelian.is_limit_of_exact_of_mono _ _ hex) _ },
        { exact exact_cokernel pushout.inr },
        { exact exact_epi_zero (cokernel.π pushout.inr) },
        { exact ((exact_iff_exact_seq _ _).2 (H₂.extract 0 2)) },
        { exact ((exact_iff_exact_seq _ _).2 (H₂.extract 1 2)) },
        { exact exact_epi_zero πh₂ } } } }
end
