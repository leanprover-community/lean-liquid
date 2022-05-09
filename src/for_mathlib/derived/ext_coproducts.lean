import for_mathlib.derived.K_projective

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A] [has_coproducts A]

open_locale zero_object

namespace homotopy_category

def coproduct_iso {α : Type v} (X : α → cochain_complex A ℤ) (i) :
  (sigma_obj X).X i ≅ sigma_obj (λ a : α, (X a).X i) := sorry

lemma coproduct_iso_inv_f {α : Type v} (X : α → cochain_complex A ℤ) (i) (Y)
  (f : sigma_obj X ⟶ Y) (a):
  sigma.ι _ a ≫ (coproduct_iso X i).inv ≫ f.f i = (sigma.ι _ a ≫ f).f i := sorry

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
    simp_rw [coproduct_iso_inv_f, (h a).comm, preadditive.comp_add,
      coproduct_iso_inv_f],
    congr' 1,
    sorry
  end }

lemma homotopic_coprod {α : Type v} (X : α → cochain_complex A ℤ) (Y)
  (f g : sigma_obj X ⟶ Y)
  (h : ∀ a : α, homotopic _ _ (sigma.ι _ a ≫ f) (sigma.ι _ a ≫ g)) :
  homotopic _ _ f g := sorry

-- Move this
lemma homotopic_of_quotient_map_eq {X Y : cochain_complex A ℤ}
  (f g : X ⟶ Y) (h : (quotient _ _).map f = (quotient _ _).map g) :
  homotopic _ _ f g :=
begin
  erw quotient.functor_map_eq_iff at h, assumption,
end

instance {α : Type v} (X : α → homotopy_category A (complex_shape.up ℤ)) :
  has_coproduct X :=
{ exists_colimit := nonempty.intro $
  { cocone := cofan.mk
      ((quotient _ _).obj $ sigma_obj (λ a, (X a).as))
      (λ a, (quotient _ _).map $ sigma.ι _ a),
    is_colimit :=
    { desc := λ S, (quotient _ _).map $ sigma.desc $ λ a, (S.ι.app a).out,
      fac' := by sorry ; begin
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
      end } } }

end homotopy_category
