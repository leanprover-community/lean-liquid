import for_mathlib.Profinite.extend
import for_mathlib.AddCommGroup.exact

import condensed.ab
import pseudo_normed_group.bounded_limits
import condensed.extr.lift_comphaus
import condensed.projective_resolution
import condensed.kernel_comparison

.

universe u

open_locale nnreal

open category_theory category_theory.limits opposite pseudo_normed_group

namespace CompHausFiltPseuNormGrp₁

variables {A B C : CompHausFiltPseuNormGrp₁.{u}}

structure exact_with_constant (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0) : Prop :=
(exact : exact ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map f) ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map g))
(cond : ∀ c : ℝ≥0, g ⁻¹' {0} ∩ (filtration B c) ⊆ f '' (filtration A (r * c)))

lemma exact_with_constant_extend {A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0)
  (hfg : ∀ S, exact_with_constant (f.app S) (g.app S) r) (S : Profinite) :
  exact_with_constant
   ((Profinite.extend_nat_trans f).app S) ((Profinite.extend_nat_trans g).app S) r :=
sorry

instance has_zero_nat_trans_CHFPNG₁ {𝒞 : Type*} [category 𝒞]
  (A B : 𝒞 ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  has_zero (A ⟶ B) :=
⟨⟨0, λ S T f, by { ext t, exact (B.map f).map_zero.symm }⟩⟩

@[simp] lemma Profinite.extend_nat_trans_zero (A B : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  Profinite.extend_nat_trans (0 : A ⟶ B) = 0 :=
sorry

lemma exact_with_constant_extend_zero_left (A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u})
  (g : B ⟶ C) (r : ℝ≥0)
  (hfg : ∀ S, exact_with_constant (0 : A.obj S ⟶ B.obj S) (g.app S) r) (S : Profinite) :
  exact_with_constant (0 : (Profinite.extend A).obj S ⟶ (Profinite.extend B).obj S)
    ((Profinite.extend_nat_trans g).app S) r :=
begin
  have := exact_with_constant_extend (0 : A ⟶ B) g r hfg S,
  simpa,
end

lemma exact_with_constant_extend_zero_right (A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u})
  (f : A ⟶ B) (r : ℝ≥0)
  (hfg : ∀ S, exact_with_constant (f.app S) (0 : B.obj S ⟶ C.obj S) r) (S : Profinite) :
  exact_with_constant ((Profinite.extend_nat_trans f).app S)
    (0 : (Profinite.extend B).obj S ⟶ (Profinite.extend C).obj S) r :=
begin
  have := exact_with_constant_extend f (0 : B ⟶ C) r hfg S,
  simpa,
end

variables (C)

lemma exact_with_constant_of_epi (f : A ⟶ B) [H : epi ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map f)]
  (r : ℝ≥0) (hf : ∀ c, filtration B c ⊆ f '' (filtration A (r * c))) :
  exact_with_constant f (0 : B ⟶ C) r :=
begin
  fsplit,
  { exact ((abelian.tfae_epi
      ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).obj C)
      ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map f)).out 0 2).mp H, },
  { intro c, exact set.subset.trans (set.inter_subset_right _ _) (hf c), }
end

variables (A) {C}

lemma exact_with_constant_of_mono (g : B ⟶ C) [hg : mono ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map g)] :
  exact_with_constant (0 : A ⟶ B) g 1 :=
begin
  fsplit,
  { exact ((abelian.tfae_mono
      ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).obj A)
      ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map g)).out 0 2).mp hg, },
  { rintro c x ⟨hx, -⟩,
    suffices : x = 0, { subst x, refine ⟨0, zero_mem_filtration _, rfl⟩, },
    simp only [set.mem_preimage, set.mem_singleton_iff] at hx,
    rw [AddCommGroup.mono_iff_injective, add_monoid_hom.injective_iff] at hg,
    exact hg _ hx, }
end

end CompHausFiltPseuNormGrp₁

namespace condensed

open CompHausFiltPseuNormGrp₁

lemma zero_iff_ExtrDisc {A B : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) :
  f = 0 ↔ (∀ S : ExtrDisc, f.val.app (op S.val) = 0) :=
begin
  split,
  { rintros ⟨rfl⟩, simp },
  { intros h,
    apply (Condensed_ExtrSheafProd_equiv Ab).functor.map_injective,
    apply (ExtrSheafProd_to_presheaf Ab).map_injective,
    ext : 2,
    apply h }
end

lemma exact_iff_ExtrDisc {A B C : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ ∀ (S : ExtrDisc),
    exact (f.1.app $ ExtrDisc_to_Profinite.op.obj (op S))
          (g.1.app $ ExtrDisc_to_Profinite.op.obj (op S)) :=
begin
  simp only [abelian.exact_iff, zero_iff_ExtrDisc, forall_and_distrib],
  refine and_congr iff.rfl _,
  apply forall_congr,
  intro S,
  symmetry,
  rw [← cancel_epi (kernel_iso g S).hom, ← cancel_mono (cokernel_iso f S).hom],
  dsimp only [functor.op_obj, ExtrDisc_to_Profinite_obj],
  simp only [category.assoc, zero_comp, comp_zero],
  erw [kernel_iso_hom_assoc, cokernel_iso_hom],
  exact iff.rfl,
end

open comphaus_filtered_pseudo_normed_group

lemma exact_of_exact_with_constant {A B C : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0) (hr : 1 ≤ r)
  (hfg : exact_with_constant f g r) :
  exact (to_Condensed.map f) (to_Condensed.map g) :=
begin
  rw exact_iff_ExtrDisc,
  intro S,
  simp only [subtype.val_eq_coe, to_Condensed_map, CompHausFiltPseuNormGrp.Presheaf.map_app,
    whisker_right_app, Ab.exact_ulift_map],
  rw AddCommGroup.exact_iff',
  split,
  { ext x s,
    simp only [subtype.val_eq_coe, CompHausFiltPseuNormGrp.presheaf.map_apply, function.comp_app,
      category_theory.comp_apply, AddCommGroup.zero_apply,
      strict_comphaus_filtered_pseudo_normed_group_hom.to_chfpsng_hom_to_fun],
    exact fun_like.congr_fun hfg.exact.w (x.1 s), },
  { rintro ⟨_, c, y₀ : S.val → filtration B c, hy₀, rfl⟩ hy,
    dsimp at hy ⊢,
    simp only [add_monoid_hom.mem_ker, add_monoid_hom.mem_range, function.comp,
      strict_comphaus_filtered_pseudo_normed_group_hom.to_chfpsng_hom_to_fun,
      CompHausFiltPseuNormGrp.presheaf.map_apply] at hy ⊢,
    let f₀ : (CompHaus.of $ filtration A (r * c)) ⟶ (CompHaus.of $ filtration B (r * c)) :=
      (CompHausFiltPseuNormGrp₁.level.obj (r * c)).map f,
    let g₀ : (CompHaus.of $ filtration B c) ⟶ (CompHaus.of $ filtration C c) :=
      (CompHausFiltPseuNormGrp₁.level.obj c).map g,
    let K : set (filtration B c) := g₀ ⁻¹' {(0 : filtration C c)},
    have K_cmpt : is_compact K := (is_closed_singleton.preimage g₀.continuous).is_compact,
    rw is_compact_iff_compact_space at K_cmpt,
    have aux : fact (c ≤ r * c),
    { refine ⟨_⟩, transitivity 1 * c, rw one_mul, exact mul_le_mul' hr le_rfl },
    resetI,
    let α : (CompHaus.of $ K) ⟶ (CompHaus.of $ filtration B (r * c)) :=
      ⟨cast_le ∘ (coe : K → filtration B c), (continuous_cast_le _ _).comp continuous_subtype_val⟩,
    let Z := pullback α f₀,
    have hZ : function.surjective (pullback.fst : Z ⟶ _),
    { rintro (b : K),
      have hb : (b : B) ∈ g ⁻¹' {0} ∩ filtration B c,
      { refine ⟨_, b.1.2⟩, have := b.2, dsimp [K] at this,
        simp only [set.mem_preimage, set.mem_singleton_iff] at this ⊢,
        exact congr_arg coe this, },
      obtain ⟨a, ha⟩ := hfg.cond c hb,
      let t : CompHaus.of punit ⟶ Z := pullback.lift
        ⟨λ _, b, continuous_const⟩ ⟨λ _, ⟨a, ha.1⟩, continuous_const⟩ _,
      swap,
      { ext ⟨⟩,
        simp only [CompHaus.coe_comp, continuous_map.coe_mk, function.comp_app, coe_cast_le],
        exact ha.2.symm, },
      refine ⟨t punit.star, _⟩,
      rw [← category_theory.comp_apply, pullback.lift_fst],
      refl, },
    let y₀' : S.val → K := λ s, ⟨y₀ s, _⟩,
    swap, { ext, rw subtype.ext_iff at hy, exact congr_fun hy s, },
    have hy₀' : continuous y₀' := continuous_subtype_mk _ hy₀,
    let x : S.val.to_CompHaus ⟶ Z := ExtrDisc.lift' _ hZ ⟨y₀', hy₀'⟩,
    have hx' : x ≫ (pullback.fst : Z ⟶ _) = ⟨y₀', hy₀'⟩ := ExtrDisc.lift_lifts' _ _ _,
    let x₀ : S.val → filtration A (r * c) := (pullback.snd : Z ⟶ _) ∘ x,
    have hx₀ : continuous x₀ := (continuous_map.continuous _).comp x.continuous,
    have hfx₀ : ∀ s : S.val, f (x₀ s) = y₀ s,
    { intro s,
      have := (@pullback.condition _ _ _ _ _ α f₀ _),
      rw fun_like.ext_iff at this,
      convert (congr_arg (coe : filtration B _ → B) (this (x s))).symm using 1,
      rw [fun_like.ext_iff] at hx',
      simp only [coe_comp, function.comp_apply] at hx' ⊢,
      rw hx', refl },
    refine ⟨⟨_, _, x₀, hx₀, rfl⟩, _⟩,
    ext s,
    exact hfx₀ s, }
end
.

@[simp] lemma to_Condensed_map_zero (A B : CompHausFiltPseuNormGrp₁.{u}) :
  to_Condensed.map (0 : A ⟶ B) = 0 :=
by { ext S s x, refl, }

lemma mono_to_Condensed_map {A B : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (hf : exact_with_constant (0 : A ⟶ A) f 1) :
  mono (to_Condensed.map f) :=
begin
  refine ((abelian.tfae_mono (to_Condensed.obj A) (to_Condensed.map f)).out 2 0).mp _,
  have := exact_of_exact_with_constant (0 : A ⟶ A) f 1 le_rfl hf,
  simpa only [to_Condensed_map_zero],
end

lemma epi_to_Condensed_map {A B : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (r : ℝ≥0) (hr : 1 ≤ r) (hf : exact_with_constant f (0 : B ⟶ B) r) :
  epi (to_Condensed.map f) :=
begin
  refine ((abelian.tfae_epi (to_Condensed.obj B) (to_Condensed.map f)).out 2 0).mp _,
  have := exact_of_exact_with_constant f (0 : B ⟶ B) r hr hf,
  simpa only [to_Condensed_map_zero]
end

end condensed
