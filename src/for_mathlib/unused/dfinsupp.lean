import data.finsupp.to_dfinsupp
import algebra.direct_sum_graded

variables {ι : Type*}
  {B : Type*} [has_zero B]

theorem dfinsupp.to_finsupp_apply [decidable_eq ι] [Π (m : B), decidable (m ≠ 0)]
  (f : Π₀ (i : ι), B) (j : ι) : f.to_finsupp j = f j := rfl

-- monoid variant
variables {M : Type*} [add_comm_monoid M]

noncomputable def dfinsupp.to_finsupp.add_monoid_hom [decidable_eq ι]
  [Π (m : M), decidable (m ≠ 0)] :
  (Π₀ (i : ι), M) →+ (ι →₀ M) :=
{ to_fun := dfinsupp.to_finsupp,
  map_zero' := begin ext, rw dfinsupp.to_finsupp_apply, refl, end,
  map_add' := λ x y, begin ext, simp [dfinsupp.to_finsupp_apply] end }

variables {β : ι → Type*} [Π i, add_comm_monoid (β i)]

open_locale direct_sum

-- This seems natural
noncomputable def dfinsupp.to_finsupp_monoid_hom [decidable_eq ι]
  [Π (m : M), decidable (m ≠ 0)] (φ : Π i, β i →+ M) : (⨁ i, β i) →+ (ι →₀ M) :=
add_monoid_hom.comp dfinsupp.to_finsupp.add_monoid_hom (dfinsupp.map_range.add_monoid_hom φ)

variables {A : ι → add_submonoid M}

-- the definition I actually want
noncomputable def direct_sum.add_submonoid_to_finsupp [decidable_eq ι]
  [Π (m : M), decidable (m ≠ 0)] : (⨁ i, A i) →+ (ι →₀ M) :=
dfinsupp.to_finsupp_monoid_hom (λ i, (A i).subtype)

theorem direct_sum.add_submonoid_to_finsupp_mem [decidable_eq ι]
  [Π (m : M), decidable (m ≠ 0)] (f : ⨁ i, A i) (j : ι) :
  direct_sum.add_submonoid_to_finsupp f j ∈ A j :=
begin
  change dfinsupp.to_finsupp _ j ∈ A j,
  simp [dfinsupp.to_finsupp_apply],
end
