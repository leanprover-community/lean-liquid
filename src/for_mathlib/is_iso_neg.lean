import for_mathlib.abelian_category
import for_mathlib.int
import for_mathlib.neg_one_pow

universes v u

open category_theory category_theory.limits
open category_theory.preadditive

variables {A : Type u} [category.{v} A] [preadditive A] {X Y : A} (f : X ⟶ Y)

-- Move This
@[simp] lemma is_iso_neg_iff : is_iso (-f) ↔ is_iso f :=
begin
  split; rintro ⟨g, hg⟩; refine ⟨⟨-g, _⟩⟩;
  simpa only [preadditive.comp_neg, preadditive.neg_comp, neg_neg] using hg,
end

-- move me
instance is_iso_neg [is_iso f] : is_iso (-f) :=
by rwa is_iso_neg_iff

-- Move This
@[simp] lemma is_iso_neg_one_pow_iff (i : ℤ) :
  is_iso (i.neg_one_pow • f) ↔ is_iso f :=
begin
  induction i using int.induction_on_iff with i,
  { simp only [int.neg_one_pow_neg_zero, one_zsmul] },
  dsimp,
  simp only [int.neg_one_pow_add, int.neg_one_pow_one, mul_neg, mul_one, neg_smul, is_iso_neg_iff],
end
