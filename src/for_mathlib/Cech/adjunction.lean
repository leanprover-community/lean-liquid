import algebraic_topology.cech_nerve

import for_mathlib.simplicial.augmented

universe u

noncomputable theory

open_locale simplicial

namespace category_theory

open category_theory.limits

variables {C : Type*} [category C]

namespace simplicial_object

variables [∀ (n : ℕ) (f : arrow C),
  has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The augmented Cech nerve construction is right adjoint to the `to_arrow` functor. -/
@[simps]
def cech_adjunction : (augmented.to_arrow : _ ⥤ arrow C) ⊣
  simplicial_object.augmented_cech_nerve :=
adjunction.mk_of_hom_equiv { hom_equiv := cech_nerve_equiv }
.

section
open simplex_category opposite limits.wide_pullback

lemma hom_ext (X : simplicial_object.augmented C) (F : arrow C)
  (f g : X ⟶ F.augmented_cech_nerve) (hl : f.left.app (op [0]) = g.left.app (op [0]))
  (hr : f.right = g.right) :
  f = g :=
begin
  apply (cech_nerve_equiv X F).symm.injective,
  dsimp only [cech_nerve_equiv_symm_apply],
  ext1,
  { simp only [equivalence_right_to_left_left],
    rw hl },
  { exact hr }
end

-- move this
@[simps]
def augmented_cech_nerve.left_obj_zero_iso (F : arrow C) :
  F.augmented_cech_nerve.left.obj (op [0]) ≅ F.left :=
{ hom := π _ ⟨0⟩,
  inv := lift F.hom (λ _, 𝟙 _) (λ _, category.id_comp _),
  hom_inv_id' :=
  begin
    ext,
    { rw [category.assoc, lift_π, category.id_comp, category.comp_id],
      cases j, congr' 2, dsimp at j ⊢, exact subsingleton.elim _ _ },
    { simp only [π_arrow, category.id_comp, limits.wide_pullback.lift_base, category.assoc], }
  end,
  inv_hom_id' := lift_π _ _ _ _ _ }
.

-- move this
lemma augmented_cech_nerve.left_map_comp_obj_zero_iso
  (F : arrow C) (n : simplex_category) (i : ulift (fin (n.len+1))) :
  F.augmented_cech_nerve.left.map (n.const i.down).op ≫ (augmented_cech_nerve.left_obj_zero_iso F).hom =
  wide_pullback.π _ i :=
begin
  rw [← iso.eq_comp_inv],
  dsimp only [arrow.augmented_cech_nerve_left, arrow.cech_nerve_map,
    augmented_cech_nerve.left_obj_zero_iso_inv],
  ext1 ⟨j⟩,
  { rw [limits.wide_pullback.lift_π, category.assoc, limits.wide_pullback.lift_π, category.comp_id],
    cases i, refl },
  { rw [limits.wide_pullback.lift_base, category.assoc, limits.wide_pullback.lift_base,
      limits.wide_pullback.π_arrow], }
end
.

@[simp]
lemma equivalence_left_to_right_left_app_zero_comp_π
  (X : simplicial_object.augmented C) (F : arrow C) (G : augmented.to_arrow.obj X ⟶ F) (i) :
  (equivalence_left_to_right X F G).left.app (op [0]) ≫ limits.wide_pullback.π _ i =
  G.left :=
begin
  dsimp only [equivalence_left_to_right_left_app, unop_op],
  rw [limits.wide_pullback.lift_π, simplex_category.hom_zero_zero ([0].const i.down),
    op_id, X.left.map_id, category.id_comp],
end
.

end

end simplicial_object

end category_theory
