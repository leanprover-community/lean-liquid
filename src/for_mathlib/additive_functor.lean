import category_theory.abelian.basic
import category_theory.preadditive.additive_functor

open category_theory category_theory.limits

variables {𝒜 ℬ : Type*} [category 𝒜] [category ℬ]
variables [preadditive 𝒜] [has_binary_biproducts 𝒜] [preadditive ℬ]
variables (F : 𝒜 ⥤ ℬ)


lemma additive_of_map_fst_add_snd
  (h : ∀ A : 𝒜, F.map (biprod.fst + biprod.snd : A ⊞ A ⟶ A) =
    F.map biprod.fst + F.map biprod.snd) :
  F.additive :=
{ map_zero' := sorry,
  map_add' := λ A B f g,
  begin
    have : f + g = biprod.lift f g ≫ (biprod.fst + biprod.snd),
    { rw [preadditive.comp_add, biprod.lift_fst, biprod.lift_snd] },
    rw [this, F.map_comp, h, preadditive.comp_add, ← F.map_comp, ← F.map_comp,
      biprod.lift_fst, biprod.lift_snd],
  end }
