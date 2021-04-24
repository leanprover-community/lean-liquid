import data.dfinsupp
import data.finsupp
import algebra.direct_sum_graded

variables {ι : Type*}
  {B : Type*} [has_zero B]

-- This would probably be enough for me to get started
-- **WARNING** Sorried data. Eric PR'ed this in #7311
def dfinsupp.to_finsupp : (Π₀ (i : ι), B) → (ι →₀ B) := sorry

-- defining property
theorem dfinsupp.to_finsupp_apply (f : Π₀ (i : ι), B) (j : ι) : f.to_finsupp j = f j := sorry

-- monoid variant
variables {M : Type*} [add_comm_monoid M]

noncomputable def dfinsupp.to_finsupp.add_monoid_hom : (Π₀ (i : ι), M) →+ (ι →₀ M) :=
{ to_fun := dfinsupp.to_finsupp,
  map_zero' := begin ext, rw dfinsupp.to_finsupp_apply, refl, end,
  map_add' := λ x y, begin ext, simp [dfinsupp.to_finsupp_apply] end }

variables {β : ι → Type*} [Π i, add_comm_monoid (β i)]

open_locale direct_sum

-- This seems natural
noncomputable def dfinsupp.to_finsupp_monoid_hom (φ : Π i, β i →+ M) : (⨁ i, β i) →+ (ι →₀ M) :=
add_monoid_hom.comp dfinsupp.to_finsupp.add_monoid_hom (dfinsupp.map_range.add_monoid_hom φ)

variables {A : ι → add_submonoid M}

-- the definition I actually want
noncomputable def direct_sum.add_submonoid_to_finsupp : (⨁ i, A i) →+ (ι →₀ M) :=
dfinsupp.to_finsupp_monoid_hom (λ i, (A i).subtype)

theorem direct_sum.add_submonoid_to_finsupp_mem (f : ⨁ i, A i) (j : ι) :
  direct_sum.add_submonoid_to_finsupp f j ∈ A j :=
begin
  change dfinsupp.to_finsupp _ j ∈ A j,
  simp [dfinsupp.to_finsupp_apply],
end
