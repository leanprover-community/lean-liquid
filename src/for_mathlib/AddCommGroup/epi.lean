import group_theory.quotient_group
import group_theory.subgroup.basic
import algebra.category.Group.abelian
import category_theory.epi_mono

-- TODO: This should be integrated in the category theory library with a construction of an
-- explicit pushout cocone, etc.

variables {A B C : Type*} [add_comm_group A] [add_comm_group B] [add_comm_group C]

def compare_in_prod (f : A →+ B) (g : A →+ C) : A →+ B × C :=
{ to_fun := λ a, (f a, - g a),
  map_zero' := by simp,
  map_add' := λ x y, by { ext, simp, simp [add_comm] } }

@[derive add_comm_group]
def add_monoid_hom.pushout (f : A →+ B) (g : A →+ C) : Type* :=
(B × C) ⧸ (compare_in_prod f g).range

abbreviation add_monoid_hom.pushout_π (f : A →+ B) (g : A →+ C) :
  B × C →+ f.pushout g := quotient_add_group.mk' _

def add_monoid_hom.pushout_inl (f : A →+ B) (g : A →+ C) :
  B →+ f.pushout g :=
{ to_fun := λ b, f.pushout_π g (b,0),
  map_zero' := by { simp, use 0, simpa } ,
  map_add' := λ x y, by { erw quotient_add_group.eq_iff_sub_mem, simp, use 0, simpa } }

def add_monoid_hom.pushout_inr (f : A →+ B) (g : A →+ C) :
  C →+ f.pushout g :=
{ to_fun := λ b, f.pushout_π g (0,b),
  map_zero' := by { simp, use 0, simpa } ,
  map_add' := λ x y, by { erw quotient_add_group.eq_iff_sub_mem, simp, use 0, simpa } }

lemma surjective_of_comp_inl_eq_comp_inr (f : A →+ B)
  (h : f.range.subtype.pushout_inl f.range.subtype =
    f.range.subtype.pushout_inr f.range.subtype) : function.surjective f :=
begin
  intros b,
  apply_fun (λ e, e b) at h,
  dsimp [add_monoid_hom.pushout_inl, add_monoid_hom.pushout_inr] at h,
  rw quotient_add_group.eq_iff_sub_mem at h,
  simp at h,
  obtain ⟨⟨a,⟨a,rfl⟩⟩,ht⟩ := h,
  dsimp [compare_in_prod] at ht,
  apply_fun (λ e, e.fst) at ht,
  use a,
  exact ht,
end

open category_theory

theorem AddCommGroup.surjective_of_epi {A B : AddCommGroup} (f : A ⟶ B) [epi f] :
  function.surjective f :=
begin
  apply surjective_of_comp_inl_eq_comp_inr,
  apply_fun AddCommGroup.of_hom,
  swap, { tidy },
  erw ← cancel_epi f,
  change add_monoid_hom.comp _ _ = add_monoid_hom.comp _ _,
  ext,
  dsimp [AddCommGroup.of_hom, add_monoid_hom.pushout_inl,
    add_monoid_hom.pushout_inr],
  rw quotient_add_group.eq_iff_sub_mem,
  simp,
  use ⟨_,⟨x,rfl⟩⟩,
  refl,
end

universes u

open category_theory category_theory.preadditive

namespace AddCommGroup

variables {X Y : AddCommGroup.{u}} (f : X ⟶ Y)

-- move this (also, it doesn't seem to be used any longer)
lemma _root_.add_monoid_hom.range_eq_top_iff {A B : Type*}
  [add_comm_group A] [add_comm_group B] (f : A →+ B) :
  f.range = ⊤ ↔ function.surjective f :=
begin
  rw [eq_top_iff],
  split,
  { rintro h x, exact h (add_subgroup.mem_top x), },
  { rintro h x -, exact h x },
end

-- instance mono_as_hom'_subtype (U : add_subgroup X) : mono ↑U.subtype :=
-- (mono_iff_ker_eq_bot _).mpr (submodule.ker_subtype U)

-- instance epi_as_hom''_mkq (U : submodule R X) : epi ↿U.mkq :=
-- (epi_iff_range_eq_top _).mpr $ submodule.range_mkq _

end AddCommGroup
