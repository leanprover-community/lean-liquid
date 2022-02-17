import for_mathlib.AddCommGroup.epi
import for_mathlib.AddCommGroup.kernels

universe u

open category_theory

namespace AddCommGroup

variables {A B C : AddCommGroup.{u}} (f : A ⟶ B) (g : B ⟶ C)

theorem exact_iff : exact f g ↔ f.range = g.ker :=
begin
  rw abelian.exact_iff' f g (kernel_is_limit _) (cokernel_is_colimit _),
  split,
  { rintro ⟨hfg, h⟩, ext x, split,
    { rintro ⟨x, rfl⟩, exact add_monoid_hom.congr_fun hfg x },
    { intro hx, rw ← quotient_add_group.eq_zero_iff, exact add_monoid_hom.congr_fun h ⟨x, hx⟩ } },
  { intro h,
    split,
    { ext x, show f x ∈ g.ker, rw ←h, simp only [add_monoid_hom.mem_range, exists_apply_eq_apply] },
    { ext ⟨x, hx⟩, dsimp [kernel_cone, cokernel_cocone],
      simpa only [comp_apply, add_subgroup.coe_subtype, add_subgroup.coe_mk,
        quotient_add_group.mk'_apply, quotient_add_group.eq_zero_iff, h] using hx, } }
end

end AddCommGroup
