import category_theory.differential_object
import category_theory.pi.basic

universes w v u

open category_theory.limits

/-! Some results in category theory that don't exist (or at least, that I couldn't find) yet -/

namespace category_theory

namespace differential_object

variables {C : Type u} [category.{v} C] [has_zero_morphisms C] [has_shift C]
  {X Y Z : differential_object C}

@[simps] def iso_app (f : X ≅ Y) : X.X ≅ Y.X :=
⟨f.hom.f, f.inv.f, by { rw [auto_param, ← comp_f, iso.hom_inv_id, id_f] },
  by { rw [auto_param, ← comp_f, iso.inv_hom_id, id_f] }⟩

end differential_object

namespace pi
variables {I : Type w} {C : I → Type u} [Π i, category.{v} (C i)]
  {X Y Z : Π i, C i}

@[simps] def iso_app (f : X ≅ Y) (i : I) : X i ≅ Y i :=
⟨f.hom i, f.inv i, by { rw [auto_param, ← comp_apply, iso.hom_inv_id, id_apply] },
  by { rw [auto_param, ← comp_apply, iso.inv_hom_id, id_apply] }⟩

end pi

end category_theory
