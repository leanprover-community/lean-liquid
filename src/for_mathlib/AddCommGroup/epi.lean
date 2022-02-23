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

lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
begin
  have aux : f.comp f.ker.subtype = f.comp 0,
  { ext x,
    simp only [add_monoid_hom.coe_comp, add_subgroup.coe_subtype, function.comp_app,
      add_monoid_hom.comp_zero, add_monoid_hom.zero_apply],
    exact x.2 },
  have := (@cancel_mono AddCommGroup _ _ _ (AddCommGroup.of f.ker) f _ f.ker.subtype _).mp aux,
  rw [eq_bot_iff],
  intros x hx,
  exact add_monoid_hom.congr_fun this ⟨x, hx⟩,
end

-- move this
lemma _root_.add_monoid_hom.range_eq_top_iff {A B : Type*}
  [add_comm_group A] [add_comm_group B] (f : A →+ B) :
  f.range = ⊤ ↔ function.surjective f :=
begin
  rw [eq_top_iff],
  split,
  { rintro h x, exact h (add_subgroup.mem_top x), },
  { rintro h x -, exact h x },
end

lemma range_eq_top_of_epi [epi f] : f.range = ⊤ :=
begin
  let g : Y →+ Y ⧸ f.range := quotient_add_group.mk' f.range,
  have aux : g.comp f = add_monoid_hom.comp 0 f,
  { ext x,
    simp only [add_monoid_hom.coe_comp, quotient_add_group.coe_mk', add_monoid_hom.zero_comp,
      add_monoid_hom.zero_apply, quotient_add_group.eq_zero_iff, add_monoid_hom.mem_range,
      exists_apply_eq_apply] },
  have := (@cancel_epi AddCommGroup _ _ _ (AddCommGroup.of $ Y ⧸ f.range) f _ g _).mp aux,
  rw eq_top_iff,
  rintro x -,
  rw [← quotient_add_group.eq_zero_iff],
  exact add_monoid_hom.congr_fun this x,
end

lemma mono_iff_ker_eq_bot : mono f ↔ f.ker = ⊥ :=
⟨λ hf, by exactI ker_eq_bot_of_mono _,
 λ hf, concrete_category.mono_of_injective _ $ (add_monoid_hom.ker_eq_bot_iff _).1 hf⟩

lemma mono_iff_injective : mono f ↔ function.injective f :=
by rw [mono_iff_ker_eq_bot, add_monoid_hom.ker_eq_bot_iff]

lemma epi_iff_range_eq_top : epi f ↔ f.range = ⊤ :=
⟨λ hf, by exactI range_eq_top_of_epi _,
 λ hf, concrete_category.epi_of_surjective _ $ (add_monoid_hom.range_eq_top_iff _).1 hf⟩

lemma epi_iff_surjective : epi f ↔ function.surjective f :=
by rw [epi_iff_range_eq_top, add_monoid_hom.range_eq_top_iff]

-- instance mono_as_hom'_subtype (U : add_subgroup X) : mono ↑U.subtype :=
-- (mono_iff_ker_eq_bot _).mpr (submodule.ker_subtype U)

-- instance epi_as_hom''_mkq (U : submodule R X) : epi ↿U.mkq :=
-- (epi_iff_range_eq_top _).mpr $ submodule.range_mkq _

end AddCommGroup
