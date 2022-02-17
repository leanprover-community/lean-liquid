import for_mathlib.Profinite.extend
import for_mathlib.AddCommGroup.exact

import condensed.ab
import pseudo_normed_group.bounded_limits

.

universe u

open_locale nnreal

open category_theory category_theory.limits opposite pseudo_normed_group

namespace CompHausFiltPseuNormGrp₁

variables {A B C : CompHausFiltPseuNormGrp₁.{u}}

structure exact_with_constant (f : A ⟶ B) (g : B ⟶ C) (Cf : ℝ≥0) : Prop :=
(exact : exact ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map f) ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map g))
(cond : ∀ c : ℝ≥0, g ⁻¹' {0} ∩ (filtration B c) ⊆ f '' (filtration A (Cf * c)))

lemma exact_with_constant_extend {A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (Cf : ℝ≥0)
  (hfg : ∀ S, exact_with_constant (f.app S) (g.app S) Cf) (S : Profinite) :
  exact_with_constant
   ((Profinite.extend_nat_trans f).app S) ((Profinite.extend_nat_trans g).app S) Cf :=
sorry

variables (C)

lemma exact_with_constant_of_epi (f : A ⟶ B) [H : epi ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map f)]
  (Cf : ℝ≥0) (hf : ∀ c, filtration B c ⊆ f '' (filtration A (Cf * c))) :
  exact_with_constant f (0 : B ⟶ C) Cf :=
begin
  fsplit,
  { exact ((abelian.tfae_epi
      ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).obj C)
      ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map f)).out 0 2).mp H, },
  { intro c, exact set.subset.trans (set.inter_subset_right _ _) (hf c), }
end

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

lemma exact_iff_ExtrDisc  {A B C : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ ∀ (S : ExtrDisc),
    exact (f.1.app $ ExtrDisc_to_Profinite.op.obj (op S))
          (g.1.app $ ExtrDisc_to_Profinite.op.obj (op S)) :=
sorry

open comphaus_filtered_pseudo_normed_group

lemma exact_of_exact_with_constant {A B C : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (Cf : ℝ≥0) (hCf : 1 ≤ Cf)
  (hfg : exact_with_constant f g Cf) :
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
    let f₀ : (CompHaus.of $ filtration A (Cf * c)) ⟶ (CompHaus.of $ filtration B (Cf * c)) :=
      (CompHausFiltPseuNormGrp₁.level.obj (Cf * c)).map f,
    let g₀ : (CompHaus.of $ filtration B c) ⟶ (CompHaus.of $ filtration C c) :=
      (CompHausFiltPseuNormGrp₁.level.obj c).map g,
    let K : set (filtration B c) := g₀ ⁻¹' {(0 : filtration C c)},
    have K_cmpt : is_compact K := (is_closed_singleton.preimage g₀.continuous).is_compact,
    rw is_compact_iff_compact_space at K_cmpt,
    have aux : fact (c ≤ Cf * c),
    { refine ⟨_⟩, transitivity 1 * c, rw one_mul, exact mul_le_mul' hCf le_rfl },
    resetI,
    let α : (CompHaus.of $ K) ⟶ (CompHaus.of $ filtration B (Cf * c)) :=
      ⟨cast_le ∘ (coe : K → filtration B c), (continuous_cast_le _ _).comp continuous_subtype_val⟩,
    let Z := pullback α f₀,
    have hZ : epi (pullback.fst : Z ⟶ _),
    { apply concrete_category.epi_of_surjective,
      rintro (b : K),
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
    let x : S.val → Z := sorry, -- use projectivity of `S.val` (do we have this for `CompHaus`?)
    have hx : continuous x, sorry,
    have hx' : (pullback.fst : Z ⟶ _) ∘ x = y₀', sorry,
    let x₀ : S.val → filtration A (Cf * c) := (pullback.snd : Z ⟶ _) ∘ x,
    have hx₀ : continuous x₀ := (continuous_map.continuous _).comp hx,
    have hfx₀ : ∀ s : S.val, f (x₀ s) = y₀ s,
    { intro s,
      have := (@pullback.condition _ _ _ _ _ α f₀ _),
      rw continuous_map.ext_iff at this,
      convert (congr_arg (coe : filtration B _ → B) (this (x s))).symm using 1,
      rw [function.funext_iff] at hx',
      simp only [coe_comp, function.comp_apply] at hx' ⊢,
      rw hx', refl },
    refine ⟨⟨_, _, x₀, hx₀, rfl⟩, _⟩,
    ext s,
    exact hfx₀ s, }
end

end condensed
