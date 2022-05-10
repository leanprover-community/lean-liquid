import for_mathlib.derived.K_projective
import for_mathlib.derived.bounded_homotopy_category
import category_theory.limits.preserves.limits

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A] [has_coproducts A]

open_locale zero_object

namespace category_theory

noncomputable
lemma is_initial_colimit {J : Type v} [small_category J] (K : J ⥤ A)
  (hK : ∀ j, is_initial (K.obj j)) [has_colimit K] :
  is_initial (colimit K) :=
{ desc := λ T, colimit.desc _ ⟨_,
  { app := λ j, (hK j).to _,
    naturality' := λ i j f, (hK _).hom_ext _ _ }⟩,
  fac' := by rintros S ⟨⟩,
  uniq' := begin
    intros S m hm, apply colimit.hom_ext, intros j,
    apply (hK _).hom_ext
  end }

lemma is_zero_colimit {J : Type v} [small_category J] (K : J ⥤ A)
  (hK : ∀ j, is_zero (K.obj j)) [has_colimit K] :
  is_zero (colimit K) :=
begin
  suffices : is_initial (colimit K),
  { let e : colimit K ≅ ⊥_ _ := (initial_iso_is_initial this).symm,
    apply is_zero_of_iso_of_zero _ e.symm,
    apply is_zero_initial },
  apply is_initial_colimit,
  intros j,
  apply is_zero.is_initial,
  apply hK,
end

end category_theory

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

noncomputable
instance {α : Type v} : preserves_colimits_of_shape (discrete α)
  (quotient A (complex_shape.up ℤ)) :=
begin
  constructor, intros K,
  apply preserves_colimit_of_preserves_colimit_cocone
    (colimit.is_colimit K),
  let T : K ⋙ quotient A _ ≅ discrete.functor
    ((λ a : α, (quotient _ _).obj (K.obj a))) := nat_iso.of_components
    (λ _, iso.refl _) _,
  swap,
  { rintros i _ ⟨⟨⟨⟩⟩⟩, dsimp, simpa },
  apply (is_colimit.precompose_inv_equiv T
    ((quotient A (complex_shape.up ℤ)).map_cocone (colimit.cocone K))).to_fun,
  let ee : colimit_cofan (λ a : α, (quotient _ _).obj (K.obj a)) ≅
    (cocones.precompose T.inv).obj
    ((quotient A (complex_shape.up ℤ)).map_cocone (colimit.cocone K)) := _,
  swap,
  { refine cocones.ext _ _,
    { apply functor.map_iso,
      refine has_colimit.iso_of_nat_iso _,
      refine nat_iso.of_components (λ _, iso.refl _) _,
      rintro i _ ⟨⟨⟨⟩⟩⟩, dsimp, simpa },
    intros i,
    dsimp [colimit_cofan, T, nat_iso.of_components,
      has_colimit.iso_of_nat_iso, is_colimit.map],
    simp only [← functor.map_comp, category.id_comp, colimit.ι_desc],
    dsimp [cocones.precompose],
    simp only [category.id_comp] },
  apply is_colimit.of_iso_colimit _ ee,
  apply is_colimit_cofan,
end

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

instance is_K_projective_colimit_cofan {α : Type v}
  (X : α → homotopy_category A (complex_shape.up ℤ))
  [∀ a, is_K_projective (X a)] : is_K_projective (colimit_cofan X).X :=
begin
  let e : (colimit_cofan X).X ≅ sigma_obj X :=
    (is_colimit_cofan X).cocone_point_unique_up_to_iso (colimit.is_colimit _),
  apply is_K_projective_of_iso _ _ e.symm,
end

instance is_quasi_iso_sigma {α : Type v}
  (X : α → homotopy_category A (complex_shape.up ℤ))
  (P : α → homotopy_category A (complex_shape.up ℤ))
  (π : Π a, P a ⟶ X a)
  [∀ a, is_quasi_iso (π a)] :
  is_quasi_iso (sigma.desc $ λ a : α, π a ≫ sigma.ι X a) :=
begin
  constructor, intros i,
  sorry, -- need to show homology commutes with coproducts.
end

end homotopy_category

namespace bounded_homotopy_category

def bounded_by (X : bounded_homotopy_category A) (n : ℤ) : Prop :=
∀ (i : ℤ), n ≤ i → is_zero (X.val.as.X i)

class uniform_bound {α : Type v} (X : α → bounded_homotopy_category A) : Prop :=
(cond [] : ∃ n : ℤ, ∀ a, (X a).bounded_by n)

noncomputable
def cofan {α : Type v} (X : α → bounded_homotopy_category A)
  [uniform_bound X] : cofan X := cofan.mk
{ val := (homotopy_category.colimit_cofan $ λ a : α, (X a).val).X,
  bdd := begin
    obtain ⟨n,hn⟩ := uniform_bound.cond X, use n, intros i hi,
    dsimp [homotopy_category.colimit_cofan],
    let e : (∐ λ (a : α), (X a).val.as).X i ≅
      (∐ λ (a : α), (X a).val.as.X i) := homotopy_category.coproduct_iso _ _,
    refine is_zero_of_iso_of_zero _ e.symm,
    apply category_theory.is_zero_colimit,
    intros j,
    apply hn j _ hi,
  end }
(λ a, (homotopy_category.colimit_cofan _).ι.app a)

noncomputable
def is_colimit_cofan {α : Type v} (X : α → bounded_homotopy_category A)
  [uniform_bound X] : is_colimit (cofan X) :=
{ desc := λ S, (homotopy_category.is_colimit_cofan
    (λ a : α, (X a).val)).desc ((forget A).map_cocone S),
  fac' := begin
    intros S j,
    erw (homotopy_category.is_colimit_cofan (λ a : α, (X a).val)).fac
      ((forget A).map_cocone S) j, refl,
  end,
  uniq' := begin
    intros S m hm,
    apply (homotopy_category.is_colimit_cofan (λ a : α, (X a).val)).hom_ext,
    intros j,
    specialize hm j,
    erw hm,
    erw (homotopy_category.is_colimit_cofan (λ a : α, (X a).val)).fac,
    refl,
  end }

instance has_coproduct_of_uniform_bound {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniform_bound X] :
  has_coproduct X :=
begin
  constructor, apply nonempty.intro,
  refine ⟨cofan X, is_colimit_cofan X⟩,
end

instance is_K_projective_sigma {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniform_bound X]
  [∀ a, homotopy_category.is_K_projective (X a).val] :
  homotopy_category.is_K_projective (sigma_obj X).val :=
begin
  let e : (sigma_obj X) ≅ (cofan X).X :=
    (colimit.is_colimit _).cocone_point_unique_up_to_iso (is_colimit_cofan X),
  let ee := (forget A).map_iso e,
  suffices : homotopy_category.is_K_projective ((forget A).obj (cofan X).X),
  { resetI, apply homotopy_category.is_K_projective_of_iso _ _ ee.symm },
  dsimp [forget, cofan],
  apply_instance,
end

open opposite

variables [enough_projectives A]

def replace_with_bound {n : ℤ} (X : bounded_homotopy_category A) (hX : X.bounded_by n) :
  bounded_homotopy_category A :=
sorry

instance is_K_projective_replace_with_bound {n : ℤ} (X : bounded_homotopy_category A)
  (hX : X.bounded_by n) :
  homotopy_category.is_K_projective (X.replace_with_bound hX).val :=
sorry

def π_with_bound {n : ℤ} (X : bounded_homotopy_category A) (hX : X.bounded_by n) :
  (X.replace_with_bound hX) ⟶ X :=
sorry

instance is_quasi_iso_π_with_bound {n : ℤ} (X : bounded_homotopy_category A)
  (hX : X.bounded_by n) :
  homotopy_category.is_quasi_iso (X.π_with_bound hX) :=
sorry

lemma replace_with_bound_bounded_by {n : ℤ} (X : bounded_homotopy_category A)
  (hX : X.bounded_by n) :
  (X.replace_with_bound hX).bounded_by n :=
sorry

def Ext_coproduct_iso
  {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniform_bound X]
  (i : ℤ) (Y) :
  ((Ext i).obj (op (sigma_obj X))).obj Y ≅
  (AddCommGroup.of (Π a : α, ((Ext i).obj (op (X a))).obj Y)) :=
sorry

end bounded_homotopy_category
