import for_mathlib.derived.K_projective
import for_mathlib.homological_complex_op
import for_mathlib.homology_iso_Ab

noncomputable theory

universes v u

open category_theory category_theory.limits category_theory.preadditive

variables {C : Type u} {ι : Type*} [category.{v} C] [abelian C] {c : complex_shape ι}

def homotopy_category.quotient_map_hom (A B : homological_complex C c) :
  (A ⟶ B) →+ ((homotopy_category.quotient C c).obj A ⟶ (homotopy_category.quotient C c).obj B) :=
add_monoid_hom.mk' (λ f, (homotopy_category.quotient C c).map f) $ λ f g, rfl

lemma quot.mk_surjective {X : Type*} (r : X → X → Prop) :
  function.surjective (quot.mk r) :=
λ x, quot.induction_on x $ λ x, ⟨x, rfl⟩

noncomputable
def homotopy.to_single [decidable_eq ι] [decidable_rel c.rel] {X : homological_complex C c} {B : C}
  {i j : ι} (r : c.rel i j)
  (f g : X ⟶ (homological_complex.single C c i).obj B) (h : X.X j ⟶ B)
  (H : f.f i = X.d i j ≫ h ≫ eq_to_hom (if_pos rfl).symm + g.f i) :
  homotopy f g :=
{ hom := λ i₁ i₂, if r' : c.rel i₂ i₁ then if e : i₂ = i then
    (X.X_eq_to_iso (c.next_eq (e ▸ r' : c.rel i i₁) r)).hom ≫ h ≫ eq_to_hom (if_pos e).symm
    else 0 else 0,
  zero' := λ _ _ e, dif_neg e,
  comm := λ k, begin
    dsimp,
    by_cases k = i,
    swap, { apply is_zero.eq_of_tgt, dsimp, rw if_neg h, exact is_zero_zero _ },
    subst h,
    rw [d_next_eq _ r, dif_pos r, dif_pos rfl, H, X.X_eq_to_iso_refl, category.id_comp],
    nth_rewrite_lhs 0 ← add_monoid.add_zero (X.d k j ≫ h ≫ eq_to_hom _),
    congr,
    delta prev_d,
    rcases c.prev k with (_|⟨i, _⟩); dsimp,
    { refl },
    { rw comp_zero, refl }
  end }

lemma homotopic_to_single_iff [decidable_eq ι] {X : homological_complex C c}
  {B : C} {i j : ι} (r : c.rel i j)
  (f g : X ⟶ (homological_complex.single C c i).obj B) :
  homotopic _ _ f g ↔
    ∃ (h : X.X j ⟶ B), f.f i = X.d i j ≫ h ≫ eq_to_hom (if_pos rfl).symm + g.f i :=
begin
  haveI : decidable_rel c.rel := λ _ _, classical.dec _,
  refine ⟨_, λ ⟨h, H⟩, ⟨homotopy.to_single r f g h H⟩⟩,
  rintro ⟨h⟩,
  use h.hom j i ≫ eq_to_hom (if_pos rfl),
  rw [category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id, ← add_zero (_ ≫ _)],
  have := h.comm i,
  rw [d_next_eq _ r] at this,
  convert this,
  delta prev_d,
  rcases c.prev i with (_|⟨j, _⟩); dsimp; simp
end

instance : decidable_rel (complex_shape.up ℤ).rel :=
λ i j, show decidable (i + 1 = j), by apply_instance

@[simps] noncomputable
def homological_complex.hom_single_iso
  (P : cochain_complex C ℤ) (B : C) (i : ℤ) :
  (P ⟶ (homological_complex.single C (complex_shape.up ℤ) i).obj B) ≃+
    (add_monoid_hom.ker ((((preadditive_yoneda.obj B).map_homological_complex
      (complex_shape.up ℤ).symm).obj P.op).d i (i - 1))) :=
{ to_fun := λ f, begin
    refine ⟨f.f i ≫ eq_to_hom (if_pos rfl), _⟩,
    change P.d (i - 1) i ≫ f.f i ≫ eq_to_hom _ = 0,
    rw ← f.comm_assoc,
    dsimp,
    rw [zero_comp, comp_zero],
  end,
  inv_fun := λ f, begin
    refine ⟨λ j, if e : j = i then
      (P.X_eq_to_iso $ e).hom ≫ f.1 ≫ eq_to_hom (if_pos e).symm else 0, _⟩,
    rintros j k (rfl : j + 1 = k),
    dsimp,
    rw comp_zero,
    split_ifs,
    { have := eq_sub_iff_add_eq.mpr h, subst this,
      rw [P.X_d_eq_to_iso_assoc, ← category.assoc, ← subtype.val_eq_coe,
        show P.d (i - 1) i ≫ f.1 = 0, from f.2, zero_comp] },
    { exact comp_zero.symm }
  end,
  left_inv := begin
    intro f,
    ext j,
    dsimp,
    split_ifs,
    { subst h, simp },
    { apply is_zero.eq_of_tgt, rw if_neg h, exact is_zero_zero _ }
  end,
  right_inv := λ f, by { ext, dsimp, simp },
  map_add' := λ f g, subtype.ext (preadditive.add_comp _ _ _ _ _ _) }

namespace bounded_homotopy_category

noncomputable
def hom_single_iso
  (P : bounded_homotopy_category C) (B : C) (i : ℤ) :
  AddCommGroup.of (P ⟶ (bounded_homotopy_category.single C i).obj B) ≅
  (((preadditive_yoneda.obj B).map_homological_complex _).obj P.val.as.op).homology i :=
begin
  refine _ ≪≫ (homology_iso _ (i+1) i (i-1) _ _).symm,
  rotate, { dsimp, refl }, { dsimp, exact sub_add_cancel _ _ },
  refine add_equiv_iso_AddCommGroup_iso.hom _ ≪≫ (AddCommGroup.homology_iso _ _ _).symm,
  refine add_equiv.surjective_congr (homological_complex.hom_single_iso P.val.as B i)
    (homotopy_category.quotient_map_hom _ _)
    (quotient_add_group.mk' _) (quot.mk_surjective _) (quot.mk_surjective _) _,
  ext f,
  dsimp,
  simp only [homotopy_category.quotient_map_hom, quotient_add_group.ker_mk,
    add_equiv.coe_to_add_monoid_hom, add_monoid_hom.mem_ker, add_subgroup.mem_comap,
    add_subgroup.coe_subtype, add_monoid_hom.mk'_apply, add_subgroup.coe_mk,
    add_equiv.coe_mk, add_monoid_hom.mem_range],
  rw ← (homotopy_category.quotient _ _).map_zero,
  any_goals { apply_instance },
  erw quotient.functor_map_eq_iff,
  rw homotopic_to_single_iff (show (complex_shape.up ℤ).rel i (i+1), from rfl),
  apply exists_congr,
  intro g,
  simp only [add_zero, quiver.hom.unop_op, linear_map.to_add_monoid_hom_coe,
    preadditive_yoneda_obj_map_apply, homological_complex.zero_f_apply,
    homological_complex.hom_single_iso_apply_coe],
  rw [← is_iso.comp_inv_eq, inv_eq_to_hom, eq_comm, category.assoc],
end

.

/-

  (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op ⋙
      (_root_.homology_functor _ _ (-i)).op).map
      (bounded_homotopy_category.lift ((of' C₁).π ≫ of'_hom f) (of' C₂).π).out).unop := by admit
-/

lemma hom_single_iso_naturality
  (P₁ P₂ : bounded_homotopy_category C) (B : C) (i : ℤ)
  (f : P₁ ⟶ P₂) :
  (preadditive_yoneda.obj _).map f.op ≫ (bounded_homotopy_category.hom_single_iso P₁ B i).hom =
  (bounded_homotopy_category.hom_single_iso P₂ B i).hom ≫
  (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op ⋙
      (_root_.homology_functor _ _ _).op).map f.out).unop :=
begin
  sorry
end

end bounded_homotopy_category
