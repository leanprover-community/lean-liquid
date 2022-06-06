import for_mathlib.homology_exact
import algebra.category.Group.abelian
import for_mathlib.homology_map

noncomputable theory

universes v u

open category_theory

@[to_additive]
lemma subgroup.comap_eq_iff {A B : Type*} [comm_group A] [comm_group B] (f : A ≃* B)
  (C : subgroup A) (D : subgroup B) :
  D.comap f.to_monoid_hom = C ↔ C.comap f.symm.to_monoid_hom = D :=
begin
  split; rintro rfl; ext,
  { simp only [subgroup.mem_comap, mul_equiv.coe_to_monoid_hom, mul_equiv.apply_symm_apply], },
  { simp only [subgroup.mem_comap, mul_equiv.coe_to_monoid_hom, mul_equiv.symm_apply_apply], }
end

@[to_additive] noncomputable
def mul_equiv.surjective_congr {A B C D : Type*}
  [comm_group A] [comm_group B] [comm_group C] [comm_group D]
  (e : A ≃* B) (f : A →* C) (g : B →* D)
  (hf : function.surjective f) (hg : function.surjective g)
  (he : g.ker.comap e.to_monoid_hom = f.ker) :
C ≃* D :=
{ to_fun := f.lift_of_surjective hf ⟨g.comp e.to_monoid_hom, λ x hx,
  by { rw ← he at hx, exact hx }⟩,
  inv_fun := g.lift_of_surjective hg ⟨f.comp e.symm.to_monoid_hom, λ x hx,
  by { rw subgroup.comap_eq_iff at he, rw ← he at hx, exact hx, }⟩,
  left_inv := λ x, begin
    obtain ⟨x, rfl⟩ := hf x,
    delta monoid_hom.lift_of_surjective,
    simp only [monoid_hom.lift_of_right_inverse_comp_apply, subtype.coe_mk, monoid_hom.comp_apply],
    convert monoid_hom.lift_of_right_inverse_comp_apply _ _ _ _ (e.to_monoid_hom x) using 1,
    exact f.congr_arg (e.symm_apply_apply x).symm,
  end,
  right_inv := λ x, begin
    obtain ⟨x, rfl⟩ := hg x,
    delta monoid_hom.lift_of_surjective,
    simp only [monoid_hom.lift_of_right_inverse_comp_apply, subtype.coe_mk, monoid_hom.comp_apply],
    convert monoid_hom.lift_of_right_inverse_comp_apply _ _ _ _ (e.symm.to_monoid_hom x) using 1,
    exact g.congr_arg (e.apply_symm_apply x).symm,
  end,
  map_mul' := λ x y, monoid_hom.map_mul _ _ _ }

@[to_additive]
def mul_equiv.quotient_congr {A B : Type*} [comm_group A] [comm_group B] (f : A ≃* B)
  (C : subgroup A) (D : subgroup B) (h : D.comap f.to_monoid_hom = C) :
A ⧸ C ≃* B ⧸ D :=
{ to_fun := quotient_group.map _ _ f.to_monoid_hom h.ge,
  inv_fun := quotient_group.map _ _ f.symm.to_monoid_hom
  begin
    refine le_of_eq _, subst h, ext,
    simp only [subgroup.mem_comap, mul_equiv.coe_to_monoid_hom, mul_equiv.apply_symm_apply],
  end,
  left_inv := λ x, begin
    induction x using quotient_group.induction_on,
    erw [quotient_group.map_coe, f.symm_apply_apply],
    refl,
  end,
  right_inv := λ x, begin
    induction x using quotient_group.induction_on,
    erw [quotient_group.map_coe, f.apply_symm_apply],
    refl,
  end,
  map_mul' := λ x y, monoid_hom.map_mul _ _ _ }
.


attribute [elementwise] iso.hom_inv_id

namespace AddCommGroup

protected noncomputable
def homology_iso {A B C : AddCommGroup.{u}} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  homology f g w ≅ AddCommGroup.of (g.ker ⧸ (f.range.comap g.ker.subtype)) :=
begin
  refine homology_iso_cokernel_lift f g w ≪≫
    AddCommGroup.cokernel_iso_quotient _ ≪≫
    add_equiv_iso_AddCommGroup_iso.hom _,
  refine add_equiv.quotient_congr _ _ _ _,
  { exact add_equiv_iso_AddCommGroup_iso.inv (AddCommGroup.kernel_iso_ker _) },
  rw add_subgroup.comap_eq_iff,
  show add_subgroup.comap (AddCommGroup.kernel_iso_ker g).inv
    (add_monoid_hom.range (limits.kernel.lift g f w)) =
    add_subgroup.comap (add_monoid_hom.ker g).subtype (add_monoid_hom.range f),
  dsimp only [AddCommGroup.kernel_iso_ker],
  have : function.injective (λ x, limits.kernel.ι g x),
  { rw [← AddCommGroup.kernel_iso_ker_hom_comp_subtype, coe_comp],
    have : function.injective (g.ker.subtype) := subtype.val_injective,
    refine this.comp _,
    refine function.has_left_inverse.injective _,
    refine ⟨(AddCommGroup.kernel_iso_ker _).inv, _⟩,
    intro y, refine category_theory.iso.hom_inv_id_apply (AddCommGroup.kernel_iso_ker g) y, },
  ext ⟨x, hx⟩,
  simp only [add_subgroup.mem_comap, add_monoid_hom.mem_range, add_subgroup.coe_subtype,
    subtype.coe_mk, ← this.eq_iff, category_theory.limits.kernel.lift_ι_apply],
end
.

variables {A₁ B₁ C₁ A₂ B₂ C₂ : AddCommGroup.{u}}
variables {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (w₁ : f₁ ≫ g₁ = 0)
variables {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (w₂ : f₂ ≫ g₂ = 0)
variables {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂} {γ : C₁ ⟶ C₂}
variables (sq1 : commsq f₁ α β f₂) (sq2 : commsq g₁ β γ g₂)

include sq1

@[simps apply]
def ker_map : ↥(add_monoid_hom.ker f₁) →+ ↥(add_monoid_hom.ker f₂) :=
add_monoid_hom.mk' (λ x, ⟨α x, by { rw [f₂.mem_ker, ← comp_apply, ← sq1.w, comp_apply], convert β.map_zero, exact x.2 }⟩) $
by { rintro ⟨a, _⟩ ⟨b, _⟩, ext, apply α.map_add, }

include sq2

noncomputable
def homology_map :
  of (↥(add_monoid_hom.ker g₁) ⧸ add_subgroup.comap (add_monoid_hom.ker g₁).subtype (add_monoid_hom.range f₁)) ⟶
  of (↥(add_monoid_hom.ker g₂) ⧸ add_subgroup.comap (add_monoid_hom.ker g₂).subtype (add_monoid_hom.range f₂)) :=
AddCommGroup.of_hom $ quotient_add_group.lift _
  ((quotient_add_group.mk' _).comp $ ker_map sq2)
begin
  rintro ⟨y, hx : g₁ y = 0⟩ ⟨x, rfl : f₁ x = y⟩,
  dsimp only [add_monoid_hom.comp_apply, ker_map_apply, quotient_add_group.mk'_apply, subtype.coe_mk],
  rw quotient_add_group.eq_zero_iff,
  refine ⟨α x, _⟩,
  rw [← comp_apply, ← sq1.w], refl
end

noncomputable
def homology_iso_hom_homology_map :
  (AddCommGroup.homology_iso f₁ g₁ w₁).hom ≫ homology_map sq1 sq2 =
  homology.map' w₁ w₂ sq1 sq2 ≫ (AddCommGroup.homology_iso f₂ g₂ w₂).hom :=
sorry

noncomputable
def homology_iso_inv_homology_map :
  (AddCommGroup.homology_iso f₁ g₁ w₁).inv ≫ homology.map' w₁ w₂ sq1 sq2 =
  homology_map sq1 sq2 ≫ (AddCommGroup.homology_iso f₂ g₂ w₂).inv :=
by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, homology_iso_hom_homology_map]

end AddCommGroup
