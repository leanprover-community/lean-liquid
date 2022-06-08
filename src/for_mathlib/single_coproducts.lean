import for_mathlib.derived.ext_coproducts

.

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A] [has_coproducts A]

namespace homological_complex

noncomputable
def sigma_single_component {α : Type v} (i : ℤ) (X : α → A) :
  (∐ (λ a, (single A (complex_shape.up ℤ) i).obj (X a))).X i ≅ ∐ X :=
{ hom := (is_colimit_of_preserves (eval _ _ i) (colimit.is_colimit
      (discrete.functor $ λ a, (single A (complex_shape.up ℤ) i).obj (X a)))).desc ⟨∐ X,
    discrete.nat_trans $ λ a, eq_to_hom (if_pos rfl) ≫ sigma.ι _ a⟩,
  inv := sigma.desc $ λ a, eq_to_hom (if_pos rfl).symm ≫
    (sigma.ι (λ (a : α), (single A (complex_shape.up ℤ) i).obj (X a)) a).f i,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

noncomputable
def sigma_single_component_of_eq {α : Type v} (j i : ℤ) (X : α → A) (h : j = i) :
  (∐ (λ a, (single A (complex_shape.up ℤ) i).obj (X a))).X j ≅ ∐ X :=
eq_to_iso (congr_arg _ h) ≪≫ sigma_single_component i X

noncomputable
def single_sigma_iso {α : Type v} (i : ℤ) (X : α → A) :
  (single A (complex_shape.up ℤ) i).obj (∐ X) ≅
  ∐ (λ a, (single A _ i).obj (X a)) :=
{ hom :=
  { f := λ j, if h : j = i then eq_to_hom (if_pos h) ≫
      sigma.desc (λ a, sigma.ι _ _ ≫ (sigma_single_component_of_eq j i X h).inv) else 0,
    comm' := sorry },
  inv := sigma.desc $ λ a,
  { f := λ j, if h : j = i then
      eq_to_hom (if_pos h) ≫
        sigma.ι _ _ ≫
        eq_to_hom (if_pos h).symm else 0,
    comm' := sorry },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

noncomputable
instance preserves_coproducts_single {α : Type v} (i : ℤ) :
  preserves_colimits_of_shape (discrete α) (single A (complex_shape.up ℤ) i) :=
preserves_coproducts_aux _
(λ X, single_sigma_iso _ _)
sorry

end homological_complex

namespace homotopy_category

noncomputable
instance preserves_coproducts_single {α : Type v} (i : ℤ) :
  preserves_colimits_of_shape (discrete α) (single A i) :=
preserves_coproducts_aux _
(λ X, (quotient _ _).map_iso
  (homological_complex.single_sigma_iso _ _) ≪≫
  preserves_colimit_iso (quotient _ _) _ ≪≫ has_colimit.iso_of_nat_iso
    (discrete.nat_iso $ λ a, iso.refl _))
sorry

end homotopy_category

namespace bounded_homotopy_category

instance uniformly_bounded_single {α : Type v} (i : ℤ) (X : α → A) :
  uniformly_bounded (λ a : α, (single A i).obj (X a)) :=
begin
  refine ⟨⟨i+1, λ a k hk, _⟩⟩,
  dsimp only [single, homotopy_category.single, functor.comp_obj, function.comp_app,
    homotopy_category.quotient_obj_as, homological_complex.single],
  rw if_neg,
  { exact is_zero_zero _ },
  { rintro rfl, linarith only [hk] }
end

instance has_coproduct_of_shape_single {α : Type v} (i : ℤ)
  (X : α → A) : has_coproduct (λ a, (single A i).obj (X a)) :=
bounded_homotopy_category.has_coproduct_of_uniform_bound _

noncomputable
def single_sigma_iso {α : Type v} (i : ℤ) (X : α → A) :
  (single A i).obj (∐ X) ≅ ∐ λ (a : α), (single A i).obj (X a) :=
let E : discrete.functor X ⋙ homotopy_category.single A i ≅
  discrete.functor (λ (a : α), (single A i).obj (X a)) ⋙ forget A :=
  discrete.nat_iso (λ a, iso.refl _) in
mk_iso $
preserves_colimit_iso (homotopy_category.single A i) (discrete.functor X) ≪≫
has_colimit.iso_of_nat_iso E ≪≫
(preserves_colimit_iso (forget A) $ discrete.functor (λ a, (single A i).obj (X a))).symm

noncomputable
instance preserves_coproducts_single {α : Type v}
  [has_coproducts A]
  (i : ℤ) :
  preserves_colimits_of_shape (discrete α) (single A i) :=
preserves_coproducts_aux _
(λ X, single_sigma_iso i X)
sorry

variables [enough_projectives A]

instance preserves_coproducts_Ext' {α : Type v} (i : ℤ) (Y : A) :
  preserves_colimits_of_shape (discrete α)
  ((Ext' i).flip.obj Y).right_op := sorry

end bounded_homotopy_category
