import for_mathlib.derived.derived_cat

open category_theory category_theory.triangulated category_theory.limits
variables (A : Type*) [category A] [abelian A] [enough_projectives A]

namespace bounded_derived_category

@[simps]
def forget : bounded_derived_category A ⥤ bounded_homotopy_category A :=
{ obj := λ X, X.val,
  map := λ _ _ f, f.val,
  map_id' := λ _ , rfl,
  map_comp' := λ _ _ _ _ _, rfl }

instance Ext_additive_fst (i : ℤ) (X : bounded_derived_category A) :
  (((Ext A i).flip.obj X).right_op).additive :=
{ map_add' := begin
    intros Y Z f g, dsimp,
    conv_rhs { rw ← op_add }, congr' 1, ext e,
    dsimp, rw preadditive.add_comp,
  end }

instance Ext_homological_fst (i : ℤ) (X : bounded_derived_category A) :
  homological_functor ((Ext A i).flip.obj X).right_op :=
category_theory.triangulated.preadditive_yoneda_op_homological (X⟦i⟧)

end bounded_derived_category

namespace homological_complex

variables {A}
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

noncomputable
def cone.π (w : ∀ i, f.f i ≫ g.f i = 0) :
  cone f ⟶ Z :=
{ f := λ i, biprod.snd ≫ g.f i,
  comm' := λ i j hij, begin
    dsimp at hij, subst j, dsimp [cone.d], rw [if_pos rfl, biprod.lift_snd_assoc],
    ext,
    { simp only [exact.w_assoc, zero_comp, category.assoc, biprod.inl_desc_assoc,
        category.id_comp, w], },
    { simp only [category.assoc, biprod.inr_snd_assoc, biprod.inr_desc_assoc, g.comm], }
  end }

def cone.π_quasi_iso (w : ∀ i, f.f i ≫ g.f i = 0) :
  quasi_iso (cone.π f g w) :=
{ is_iso := λ i, begin
    sorry
  end }

end homological_complex
