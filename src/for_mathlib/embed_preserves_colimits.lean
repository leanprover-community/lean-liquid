import for_mathlib.complex_extend
import for_mathlib.homological_complex_abelian

universes v u

noncomputable theory

open category_theory category_theory.limits
open_locale zero_object

variables {ι₁ ι₂ : Type*} {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂)
  {C : Type*} [category C] [preadditive C] [has_zero_object C]
  {J : Type*} [category J] [has_colimits_of_shape J C]

instance : preserves_colimits_of_shape J
  (homological_complex.embed e : homological_complex C c₁ ⥤ _) :=
⟨λ G, begin
  suffices : ∀ i₂, preserves_colimit G (homological_complex.embed e ⋙
    homological_complex.eval C c₂ i₂),
  { constructor,
    intros s hs,
    refine homological_complex.is_colimit_of_is_colimit_eval _ _ _,
    intro i₂,
    haveI := this i₂,
    change is_colimit ((homological_complex.embed e ⋙
      homological_complex.eval C c₂ i₂).map_cocone s),
    apply is_colimit_of_preserves,
    exact hs, },
  intro i₂,
  by_cases hi₂ : ∃ i₁ : ι₁, i₂ = e.f i₁,
  { let i₁ := hi₂.some,
    have hi₂' : i₂ = e.f i₁ := hi₂.some_spec,
    have α := iso_whisker_left _ (homological_complex.congr_eval _ _ _ _ hi₂') ≪≫
      homological_complex.embed_comp_eval C e i₁,
    exact preserves_colimit_of_nat_iso _ α.symm, },
  { have α : homological_complex.embed e ⋙ homological_complex.eval C c₂ i₂ ≅ 0,
    { refine is_zero.iso _ (is_zero_zero _),
      rw is_zero.iff_id_eq_zero,
      ext X,
      simp only [nat_trans.id_app, nat_trans.app_zero, ← is_zero.iff_id_eq_zero],
      dsimp [homological_complex.embed, homological_complex.embed.obj],
      rw e.r_none i₂ hi₂,
      apply is_zero_zero,
    },
    haveI : preserves_colimit G (0 : homological_complex C c₁ ⥤ C),
    { constructor,
      intros s hs,
      exact
      { desc := λ s, 0,
        fac' := λ s j, begin
          apply is_zero.eq_of_src,
          exact (functor.is_zero_iff 0).mp (is_zero_zero _) _,
        end,
        uniq' := λ s m hm, begin
          apply is_zero.eq_of_src,
          exact (functor.is_zero_iff 0).mp (is_zero_zero _) _,
        end, }, },
    exact preserves_colimit_of_nat_iso _ α.symm, },
end⟩
