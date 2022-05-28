import algebraic_topology.cech_nerve

open category_theory opposite

-- dedup with `cech_iso_zero` in `src/prop819.lean`

noncomputable
def arrow.cech_nerve_obj_0
  {C : Type*} [category C] (F : arrow C) [limits.has_limits C] :
  F.cech_nerve.obj (op (simplex_category.mk 0)) ≅ F.left :=
{ hom := limits.wide_pullback.π _ ⟨0⟩,
  inv := limits.wide_pullback.lift F.hom (λ _, 𝟙 _) (by simp only [category.id_comp, forall_const]),
  hom_inv_id' := begin
    apply limits.wide_pullback.hom_ext,
    { intro i,
      simp only [limits.wide_pullback.lift_π, category.id_comp, category.comp_id, category.assoc],
      cases i, cases i, congr, dsimp, simp only [eq_iff_true_of_subsingleton] },
    { simp only [category.id_comp, category.assoc, limits.wide_pullback.lift_base, limits.wide_pullback.π_arrow] }
  end,
  inv_hom_id' := limits.wide_pullback.lift_π _ _ _ _ _ }
