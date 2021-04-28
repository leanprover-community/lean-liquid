import category_theory.isomorphism
import category_theory.opposites

namespace category_theory

open opposite

variables {C : Type*} [category C]

@[simps]
def iso.unop {X Y : Cᵒᵖ} (f : X ≅ Y) : (Y.unop ≅ X.unop) :=
{ hom := f.hom.unop,
  inv := f.inv.unop,
  hom_inv_id' := by simp only [← unop_comp, f.inv_hom_id, unop_id],
  inv_hom_id' := by simp only [← unop_comp, f.hom_inv_id, unop_id] }

@[simps]
def iso.remove_op {X Y : C} (f : (op X) ≅ (op Y)) : Y ≅ X :=
{ hom := f.hom.unop,
  inv := f.inv.unop,
  hom_inv_id' := by simp only [← unop_comp, f.inv_hom_id, unop_id_op],
  inv_hom_id' := by simp only [← unop_comp, f.hom_inv_id, unop_id_op] }

@[simp] lemma iso.unop_op {X Y : Cᵒᵖ} (f : X ≅ Y) : f.unop.op = f :=
by ext; refl

@[simp] lemma iso.op_unop {X Y : C} (f : X ≅ Y) : f.op.unop = f :=
by ext; refl

end category_theory
