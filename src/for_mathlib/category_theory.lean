import category_theory.differential_object
import category_theory.pi.basic

universes w w₁ w₂ v v₁ v₂ u u₁ u₂

open category_theory.limits

/-! Some results in category theory that don't exist (or at least, that I couldn't find) yet.
 This should maybe be split up in different files. -/

namespace category_theory

namespace differential_object

variables {C : Type u₁} [category.{v₁} C] [has_zero_morphisms C] [has_shift C]
          {D : Type u₂} [category.{v₂} D] [has_zero_morphisms D] [has_shift D]
  {X Y Z : differential_object C}

/--
An isomorphism of differential objects gives an isomorphism of the underlying objects.
-/
@[simps] def iso_app (f : X ≅ Y) : X.X ≅ Y.X :=
⟨f.hom.f, f.inv.f, by { dsimp, rw [← comp_f, iso.hom_inv_id, id_f] },
  by { dsimp, rw [← comp_f, iso.inv_hom_id, id_f] }⟩

/--
A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero morphisms
can be lifted to a functor `differential_object C ⥤ differential_object D`.
-/
@[simps]
def functor (F : C ⥤ D) (η : (shift C).functor.comp F ⟶ F.comp (shift D).functor)
  (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) :
  differential_object C ⥤ differential_object D :=
{ obj := λ X, { X := F.obj X.X,
    d := F.map X.d ≫ η.app X.X,
    d_squared' := begin
      dsimp, rw [functor.map_comp, ← functor.comp_map F (shift D).functor],
      slice_lhs 2 3 { rw [← η.naturality X.d] },
      rw [functor.comp_map],
      slice_lhs 1 2 { rw [← F.map_comp, X.d_squared, hF] },
      rw [zero_comp, zero_comp],
    end },
  map := λ X Y f, { f := F.map f.f,
    comm' := begin
      dsimp,
      slice_lhs 2 3 { rw [← functor.comp_map F (shift D).functor, ← η.naturality f.f] },
      slice_lhs 1 2 { rw [functor.comp_map, ← F.map_comp, f.comm, F.map_comp] },
      rw [category.assoc]
    end },
  map_id' := by { intros, ext, simp },
  map_comp' := by { intros, ext, simp }, }

end differential_object

namespace pi
variables {I : Type w} {C : I → Type u} [Π i, category.{v} (C i)]
  {X Y Z : Π i, C i}

@[simps] def iso_app (f : X ≅ Y) (i : I) : X i ≅ Y i :=
⟨f.hom i, f.inv i, by { rw [auto_param, ← comp_apply, iso.hom_inv_id, id_apply] },
  by { rw [auto_param, ← comp_apply, iso.inv_hom_id, id_apply] }⟩

end pi

end category_theory
