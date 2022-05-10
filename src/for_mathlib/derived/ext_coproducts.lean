import for_mathlib.derived.K_projective
import category_theory.limits.preserves.limits

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A] [has_coproducts A]

open_locale zero_object

namespace homotopy_category

noncomputable
def coproduct_iso {α : Type v} (X : α → cochain_complex A ℤ) (i) :
  (sigma_obj X).X i ≅ sigma_obj (λ a : α, (X a).X i) :=
(category_theory.preserves_colimit_iso (homological_complex.eval A
  (complex_shape.up ℤ) i) (discrete.functor X)) ≪≫
  has_colimit.iso_of_nat_iso
  (nat_iso.of_components (λ _, iso.refl _) begin
    rintros i _ ⟨⟨⟨⟩⟩⟩,
    simp,
  end)

@[simp, reassoc]
lemma coproduct_ι_coproduct_iso_inv {α : Type v} (X : α → cochain_complex A ℤ) (i) (a) :
  sigma.ι _ a ≫ (coproduct_iso X i).inv = ((sigma.ι X a : _ ⟶ _)).f i :=
begin
  dsimp [coproduct_iso, has_colimit.iso_of_nat_iso,
    is_colimit.map, preserves_colimit_iso, is_colimit.cocone_point_unique_up_to_iso],
  simp, dsimp, simp,
end

@[simp, reassoc]
lemma coproduct_ι_coproduct_iso_hom {α : Type v} (X : α → cochain_complex A ℤ) (i) (a : α) :
  (sigma.ι X a : _ ⟶ _).f i ≫ (coproduct_iso X i).hom = sigma.ι _ a :=
begin
  dsimp [coproduct_iso, has_colimit.iso_of_nat_iso,
    is_colimit.map, preserves_colimit_iso, is_colimit.cocone_point_unique_up_to_iso],
  slice_lhs 0 1
  { erw (is_colimit_of_preserves (homological_complex.eval A (complex_shape.up ℤ) i)
    (colimit.is_colimit (discrete.functor X))).fac },
  simp, dsimp, simp,
end

noncomputable
def homotopy_coprod {α : Type v} (X : α → cochain_complex A ℤ) (Y)
  (f g : sigma_obj X ⟶ Y)
  (h : Π a, homotopy (sigma.ι _ a ≫ f) (sigma.ι _ a ≫ g)) :
  homotopy f g :=
{ hom := λ i j, (coproduct_iso X i).hom ≫
    (sigma.desc $ λ a, (h a).hom _ _),
  zero' := begin
    intros i j hh,
    simp only [preadditive.is_iso.comp_left_eq_zero],
    apply colimit.hom_ext, intros a,
    simp only [colimit.ι_desc, cofan.mk_ι_app, comp_zero, (h a).zero' i j hh],
  end,
  comm := begin
    intros i,
    rw ← cancel_epi (coproduct_iso X i).inv,
    apply colimit.hom_ext, intros a,
    simp only [coproduct_ι_coproduct_iso_inv_assoc, homological_complex.cochain_complex_d_next,
      homological_complex.cochain_complex_prev_d, category.assoc, preadditive.comp_add,
      homological_complex.hom.comm_assoc, coproduct_ι_coproduct_iso_hom_assoc,
      colimit.ι_desc, cofan.mk_ι_app, colimit.ι_desc_assoc],
    have := (h a).comm i,
    dsimp at this,
    rw this,
    simp only [homological_complex.cochain_complex_d_next,
      homological_complex.cochain_complex_prev_d],
  end }

lemma homotopic_coprod {α : Type v} (X : α → cochain_complex A ℤ) (Y)
  (f g : sigma_obj X ⟶ Y)
  (h : ∀ a : α, homotopic _ _ (sigma.ι _ a ≫ f) (sigma.ι _ a ≫ g)) :
  homotopic _ _ f g :=
begin
  constructor,
  apply homotopy_coprod,
  intros a,
  exact (h a).some,
end

-- Move this
lemma homotopic_of_quotient_map_eq {X Y : cochain_complex A ℤ}
  (f g : X ⟶ Y) (h : (quotient _ _).map f = (quotient _ _).map g) :
  homotopic _ _ f g :=
begin
  erw quotient.functor_map_eq_iff at h, assumption,
end

noncomputable
def colimit_cofan {α : Type v} (X : α → homotopy_category A (complex_shape.up ℤ)) :
  cofan X :=
cofan.mk
((quotient _ _).obj $ sigma_obj (λ a, (X a).as))
(λ a, (quotient _ _).map $ sigma.ι _ a)

noncomputable
def is_colimit_cofan {α : Type v} (X : α → homotopy_category A (complex_shape.up ℤ)) :
  is_colimit (colimit_cofan X) :=
{ desc := λ S, (quotient _ _).map $ sigma.desc $ λ a, (S.ι.app a).out,
  fac' := begin
    intros S j,
    dsimp,
    erw [← (quotient A (complex_shape.up ℤ)).map_comp, colimit.ι_desc],
    dsimp [quotient],
    simp,
  end,
  uniq' := begin
    intros S m hm,
    let mm := m.out,
    have : (quotient _ _).map mm = m, by simp,
    rw ← this,
    apply quot.sound,
    apply quotient.comp_closure.of,
    apply homotopic_coprod,
    intros a,
    specialize hm a, rw ← this at hm, dsimp at hm,
    erw [← (quotient A (complex_shape.up ℤ)).map_comp] at hm,
    erw colimit.ι_desc,
    dsimp,
    have : S.ι.app a = (quotient _ _).map (S.ι.app a).out, by simp,
    rw this at hm,
    apply homotopic_of_quotient_map_eq,
    exact hm
  end }

instance {α : Type v} (X : α → homotopy_category A (complex_shape.up ℤ)) :
  has_coproduct X :=
{ exists_colimit := nonempty.intro $ ⟨colimit_cofan _, is_colimit_cofan _⟩ }

instance is_K_projective_sigma {α : Type v}
  (X : α → homotopy_category A (complex_shape.up ℤ))
  [∀ a, is_K_projective (X a)] : is_K_projective (sigma_obj X) :=
begin
  constructor,
  introsI Y hY f,
  apply colimit.hom_ext,
  intros a,
  rw comp_zero,
  apply is_K_projective.cond Y,
  dsimp, apply_instance,
end

end homotopy_category
