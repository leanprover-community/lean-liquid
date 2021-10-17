import analysis.normed.group.SemiNormedGroup.kernels
import algebra.homology.additive

namespace SemiNormedGroup

protected class strict_iso {A B : SemiNormedGroup} (f : A ≅ B) :=
(strict_hom' : ∀ a : A, ∥f.hom a∥₊ = ∥a∥₊)

@[simp]
lemma strict_iso_hom {A B : SemiNormedGroup} (f : A ≅ B) [strict_iso f] (a : A) :
  ∥f.hom a∥₊ = ∥a∥₊ := strict_iso.strict_hom' _

@[simp]
lemma strict_iso_inv {A B : SemiNormedGroup} (f : A ≅ B) [strict_iso f] (b : B) :
  ∥f.inv b∥₊ = ∥b∥₊ :=
begin
  have : b = f.hom (f.inv b),
  { change b = (f.inv ≫ f.hom) b, simp },
  conv_rhs {rw this},
  rw strict_iso_hom,
end

end SemiNormedGroup

structure strict_iso (C D : cochain_complex SemiNormedGroup ℕ) :=
(iso : C ≅ D)
[is_strict : ∀ i : ℕ, SemiNormedGroup.strict_iso $ (homological_complex.eval _ _ i).map_iso iso]

instance (C D : cochain_complex SemiNormedGroup ℕ) (f : strict_iso C D) (n : ℕ) :
  SemiNormedGroup.strict_iso ((homological_complex.eval _ _ n).map_iso f.iso) := f.is_strict _
