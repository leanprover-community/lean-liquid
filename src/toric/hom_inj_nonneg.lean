import toric.is_inj_nonneg

open function

variables {N Z : Type*}

/--  The ring homomorphism `f : N → Z` is injective and its image only contains
non-negative elements. -/
structure is_inj_nonneg_hom [semiring N] [semiring Z] [has_le Z] (f : N →+* Z) : Prop :=
(inj : injective f)
(map_nonneg : ∀ n : N, 0 ≤ f n)

namespace is_inj_nonneg_hom

variable (Z)

lemma nat [ordered_semiring Z] [nontrivial Z] :
  is_inj_nonneg (nat.cast_ring_hom Z) :=
⟨@nat.cast_injective Z _ _ ordered_semiring.to_char_zero, λ n, nat.cast_nonneg n⟩

lemma nnR_ocr [ordered_comm_semiring Z] :
  is_inj_nonneg (algebra_map (nnR Z) Z) := --tidy works
⟨subtype.coe_injective, λ n, n.2⟩

lemma nnR_int_int : is_inj_nonneg (algebra_map (nnR ℤ) ℤ) :=
by convert nnR_ocr ℤ

end is_inj_nonneg_hom
