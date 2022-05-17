import algebra.category.Group.abelian
import algebra.group.ulift

universe u

def Ab.pt {X : Ab.{u}} (x : X) :
  AddCommGroup.of (ulift.{u} ℤ) ⟶ X :=
{ to_fun := λ a, zmultiples_add_hom _ x a.down,
  map_zero' := by simp,
  map_add' := λ a b, by rw [ulift.add_down, add_monoid_hom.map_add] }

lemma Ab.pt_apply {X : Ab.{u}} (x : X) (n : ℤ) : Ab.pt x ⟨n⟩ = n • x :=
by simp only [Ab.pt, zmultiples_add_hom_apply, add_monoid_hom.coe_mk]

lemma Ab.pt_apply' {X : Ab.{u}} (x : X) : Ab.pt x ⟨1⟩ = x :=
by rw [Ab.pt_apply, one_smul]

lemma Ab.pt_comp {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) :
  Ab.pt x ≫ f = Ab.pt (f x) :=
begin
  ext ⟨n⟩, simp only [Ab.pt_apply, category_theory.comp_apply, map_zsmul],
end

lemma Ab.apply_eq_pt_comp {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) :
  f x = (Ab.pt x ≫ f) ⟨1⟩ :=
by rw [category_theory.comp_apply, Ab.pt_apply']

lemma Ab.apply_eq_zero {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) :
  f x = 0 ↔ Ab.pt x ≫ f = 0 :=
begin
  split,
  { intro h, ext ⟨n⟩,
    simp only [category_theory.comp_apply, AddCommGroup.zero_apply, Ab.pt_apply,
      map_zsmul, h, smul_zero], },
  { intro h, rw [Ab.apply_eq_pt_comp, h, AddCommGroup.zero_apply], }
end
