import category_theory.limits.shapes.wide_pullbacks
import category_theory.concrete_category
import topology.category.Profinite
.

universe variables v u

open category_theory category_theory.limits category_theory.limits.wide_pullback function

namespace Profinite
namespace wide_pullback

/-
lemma ext {B : Profinite} {ι : Type*} {X : ι → Profinite} {f : Π (j : ι), X j ⟶ B}
  [has_wide_pullback B X f]
  (x y : wide_pullback B X f) (h₀ : base f x = base f y) (h : ∀ j, π f j x = π f j y) :
  x = y :=
begin
  let gx : of punit ⟶ wide_pullback B X f := ⟨const _ x, continuous_const⟩,
  let gy : of punit ⟶ wide_pullback B X f := ⟨const _ y, continuous_const⟩,
  suffices : gx = gy,
  { show gx punit.star = gy punit.star, rw this },
  apply wide_pullback.hom_ext,
  { intro j, ext1, exact h j, },
  { ext1, exact h₀ }
end

lemma ext_iff {B : Profinite} {ι : Type*} {X : ι → Profinite} {f : Π (j : ι), X j ⟶ B}
  [has_wide_pullback B X f]
  (x y : wide_pullback B X f) :
  x = y ↔ (base f x = base f y ∧ ∀ j, π f j x = π f j y) :=
begin
  refine ⟨_, _⟩,
  { rintro rfl, exact ⟨rfl, λ _, rfl⟩ },
  { rintro ⟨h₀, h⟩, apply ext x y h₀ h },
end

lemma ext' {B : Profinite} {ι : Type*} [hι : nonempty ι]
  {X : ι → Profinite} {f : Π (j : ι), X j ⟶ B} [has_wide_pullback B X f]
  (x y : wide_pullback B X f) (h : ∀ j, π f j x = π f j y) :
  x = y :=
begin
  apply ext x y _ h,
  unfreezingI { obtain ⟨j⟩ := hι },
  simp only [← π_arrow f j, coe_comp, comp, h],
end

lemma ext_iff' {B : Profinite} {ι : Type*} [nonempty ι]
  {X : ι → Profinite} {f : Π (j : ι), X j ⟶ B} [has_wide_pullback B X f]
  (x y : wide_pullback B X f) :
  x = y ↔ (∀ j, π f j x = π f j y) :=
by { refine ⟨_, ext' x y⟩, rintro rfl _, refl }

-/
end wide_pullback
end Profinite
