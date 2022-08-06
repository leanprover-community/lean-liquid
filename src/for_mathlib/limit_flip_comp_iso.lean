import category_theory.limits.fubini

open category_theory

namespace category_theory.limits

universes v u
variables {C : Type u} [category.{v} C]

noncomputable
def limit_flip_comp_lim_iso_limit_comp_lim'
  {J : Type*} [category J]
  [has_limits_of_shape J C]
  {K : Type*} [category K]
  [has_limits_of_shape K C]
  (F : J ⥤ K ⥤ C) : limit (F.flip ⋙ lim) ≅ limit (F ⋙ lim) :=
{ hom := limit.lift (F ⋙ lim) ⟨limit (F.flip ⋙ lim),
  { app := λ j, limit.lift (F.obj j) ⟨limit (F.flip ⋙ lim),
    { app := λ k, limit.π _ k ≫ limit.π _ j,
      naturality' := begin
        intros k1 k2 f,
        dsimp, simp only [category.id_comp, category.assoc],
        rw ← limit.w _ f,
        simp,
      end }⟩,
    naturality' := begin
      intros j1 j2 f,
      ext,
      dsimp,
      simp only [category.id_comp, category.assoc, limit.lift_π, limit.lift_map,
        cones.postcompose_obj_π, nat_trans.comp_app],
      rw ← limit.w _ f,
      refl,
    end }⟩,
  inv := limit.lift (F.flip ⋙ lim) ⟨limit (F ⋙ lim),
  { app := λ k, limit.lift (F.flip.obj k) ⟨limit (F ⋙ lim),
    { app := λ j, limit.π _ j ≫ limit.π _ k,
      naturality' := begin
        intros j1 j2 f,
        dsimp, simp only [category.id_comp, category.assoc],
        rw ← limit.w _ f,
        simp,
      end }⟩,
    naturality' := begin
      intros k1 k2 f,
      ext,
      dsimp,
      simp only [category.id_comp, category.assoc, limit.lift_π, limit.lift_map,
        cones.postcompose_obj_π, nat_trans.comp_app],
      rw ← limit.w _ f,
      refl,
    end }⟩,
  hom_inv_id' := begin
    ext, dsimp, simp,
  end,
  inv_hom_id' := begin
    ext, dsimp, simp,
  end }

.

@[simp, reassoc]
lemma limit_flip_comp_lim_iso_limit_comp_lim'_hom_π_π {J : Type*} [category J]
  [has_limits_of_shape J C]
  {K : Type*} [category K]
  [has_limits_of_shape K C]
  (F : J ⥤ K ⥤ C) (j) (k) :
  (limit_flip_comp_lim_iso_limit_comp_lim' F).hom ≫ limit.π _ j ≫ limit.π _ k =
  limit.π _ k ≫ limit.π _ j :=
begin
  dsimp [limit_flip_comp_lim_iso_limit_comp_lim'],
  simp,
end

@[simp, reassoc]
lemma limit_flip_comp_lim_iso_limit_comp_lim'_inv_π_π {J : Type*} [category J]
  [has_limits_of_shape J C]
  {K : Type*} [category K]
  [has_limits_of_shape K C]
  (F : J ⥤ K ⥤ C) (j) (k) :
  (limit_flip_comp_lim_iso_limit_comp_lim' F).inv ≫ limit.π _ j ≫ limit.π _ k =
  limit.π _ k ≫ limit.π _ j :=
begin
  dsimp [limit_flip_comp_lim_iso_limit_comp_lim'],
  simp,
end

end category_theory.limits
