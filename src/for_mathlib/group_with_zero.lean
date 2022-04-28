import algebra.group_with_zero
import tactic

lemma pow_add₀ {R : Type*} [group_with_zero R] {r : R} (hr : r ≠ 0) (a b : ℤ) :
  r ^ (a + b) = r ^ a * r ^ b :=
begin
  obtain ⟨u, rfl⟩ : ∃ u : units R, r = u := ⟨units.mk0 r hr, units.coe_mk0 hr⟩,
  norm_cast,
  exact zpow_add u a b,
end
