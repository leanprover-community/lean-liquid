import category_theory.types
import category_theory.const
import category_theory.functor_category
import category_theory.limits.shapes.products
import category_theory.epi_mono

namespace category_theory

open category_theory.limits

universes v u₁ u₂
variables {C : Type u₁} [category.{v} C] {D : Type u₂} [category.{v} D]
variables [∀ (a b : C), has_coproducts_of_shape (a ⟶ b) D]

@[simps]
noncomputable
def lift_eval (b : C) (a : D) :
  C ⥤ D :=
{ obj := λ t, ∐ (λ i : b ⟶ t, a),
  map := λ X Y f, sigma.desc $ λ g, sigma.ι (λ (i : b ⟶ Y), a) $ g ≫ f,
  map_id' := λ X, by {
    ext, simp only [cofan.mk_ι_app, colimit.ι_desc, category.comp_id], congr' 1, simp },
  map_comp' := λ X Y Z f g, by {
    ext, simp only [cofan.mk_ι_app, colimit.ι_desc_assoc, colimit.ι_desc], congr' 1, simp } }

@[simps]
noncomputable
def lift_eval_hom_equiv (b : C) (a : D) (F : C ⥤ D) :
  (lift_eval b a ⟶ F) ≃ (a ⟶ ((evaluation _ _).obj b).obj F) :=
{ to_fun := λ η, sigma.ι (λ i : b ⟶ b, a) (𝟙 _) ≫ η.app _,
  inv_fun := λ f, { app := λ X, sigma.desc $ λ g, f ≫ F.map g },
  left_inv := begin
    intros η,
    ext,
    simp only [cofan.mk_ι_app, colimit.ι_desc, category.assoc],
    simp only [← η.naturality, ← category.assoc,cofan.mk_ι_app,
      colimit.ι_desc, lift_eval_map],
    congr' 2,
    simp,
  end,
  right_inv := by tidy }

variable (D)
noncomputable
def lift_evaluation (a : C) : D ⥤ C ⥤ D :=
adjunction.left_adjoint_of_equiv (lift_eval_hom_equiv a) $ by tidy

noncomputable
def evaluation_adjunction (a : C) : lift_evaluation D a ⊣ (evaluation _ _).obj a :=
adjunction.adjunction_of_equiv_left _ _

noncomputable
instance (a : C) : is_right_adjoint ((evaluation C D).obj a) :=
⟨_, evaluation_adjunction _ _⟩

lemma mono_iff_app_mono {F G : C ⥤ D} (η : F ⟶ G) :
  mono η ↔ (∀ X, mono (η.app X)) :=
begin
  split,
  { intros h X,
    change mono (((evaluation _ _).obj X).map η),
    apply right_adjoint_preserves_mono,
  }
end

end category_theory
