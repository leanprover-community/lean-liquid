import category_theory.abelian.basic
import category_theory.preadditive.additive_functor

open category_theory category_theory.limits

namespace category_theory

variables {𝒜 ℬ : Type*} [category 𝒜] [category ℬ]
variables [preadditive 𝒜] [preadditive ℬ]
variables (F : 𝒜 ⥤ ℬ)
variables {A B : 𝒜} (C : 𝒜)

section is_biprod_vars

variables (inl : A ⟶ C) (inr : B ⟶ C) (fst : C ⟶ A) (snd : C ⟶ B)

structure is_biprod :=
(inl_fst : inl ≫ fst = 𝟙 _)
(inr_snd : inr ≫ snd = 𝟙 _)
(inl_snd : inl ≫ snd = 0)
(inr_fst : inr ≫ fst = 0)
(total : fst ≫ inl + snd ≫ inr = 𝟙 _)

variables {inl inr fst snd}

namespace is_biprod

@[simps] noncomputable
def iso_biprod [has_binary_biproduct A B]
  (h : is_biprod C inl inr fst snd) : C ≅ A ⊞ B :=
{ hom := biprod.lift fst snd,
  inv := biprod.desc inl inr,
  hom_inv_id' := by rw [biprod.lift_desc, h.total],
  inv_hom_id' := by { ext;
    simp only [h.inl_fst, h.inl_snd, h.inr_fst, h.inr_snd,
      biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      biprod.lift_fst, biprod.lift_snd, category.comp_id,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc, category.assoc], } }

end is_biprod

namespace functor

def map_is_biprod [F.additive] (h : is_biprod C inl inr fst snd) :
  is_biprod (F.obj C) (F.map inl) (F.map inr) (F.map fst) (F.map snd) :=
{ inl_fst := by rw [← F.map_comp, h.inl_fst, F.map_id],
  inr_snd := by rw [← F.map_comp, h.inr_snd, F.map_id],
  inl_snd := by rw [← F.map_comp, h.inl_snd, F.map_zero],
  inr_fst := by rw [← F.map_comp, h.inr_fst, F.map_zero],
  total := by rw [← F.map_comp, ← F.map_comp, ← F.map_add, h.total, F.map_id] }

end functor

end is_biprod_vars

namespace biprod

variables (A B)

@[simps] noncomputable
def is_biprod [has_binary_biproduct A B] :
  is_biprod (A ⊞ B) biprod.inl biprod.inr biprod.fst biprod.snd :=
{ inl_fst := biprod.inl_fst,
  inr_snd := biprod.inr_snd,
  inl_snd := biprod.inl_snd,
  inr_fst := biprod.inr_fst,
  total := biprod.total }

end biprod

end category_theory
