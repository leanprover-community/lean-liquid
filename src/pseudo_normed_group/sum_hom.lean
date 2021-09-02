import rescale.pseudo_normed_group

noncomputable theory

open_locale nnreal big_operators
local attribute [instance] type_pow

section

variables {r' : ℝ≥0} (M : Type*) (N : ℕ)

namespace profinitely_filtered_pseudo_normed_group

variables [profinitely_filtered_pseudo_normed_group M]

def unrescale (N : ℝ≥0) (M : Type*) [profinitely_filtered_pseudo_normed_group M] :
  comphaus_filtered_pseudo_normed_group_hom (rescale N M) M :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_bound (add_monoid_hom.id _) N⁻¹
begin
  intro c,
  refine ⟨λ x hx, _, _⟩,
  { rwa mul_comm },
  { haveI : fact (c * N⁻¹ ≤ N⁻¹ * c) := ⟨(mul_comm _ _).le⟩,
    exact comphaus_filtered_pseudo_normed_group.continuous_cast_le (c * N⁻¹) (N⁻¹ * c) },
end

def rescale_proj (i : fin N) :
  comphaus_filtered_pseudo_normed_group_hom (rescale N (M ^ N)) M :=
(comphaus_filtered_pseudo_normed_group.pi_proj i).comp (unrescale N _)

lemma rescale_proj_bound_by (i : fin N) : (rescale_proj M N i).bound_by N⁻¹ :=
by { intros c x hx, rw [rescale.mem_filtration, mul_comm] at hx, exact hx i }

def sum_hom (N : ℕ) :
  comphaus_filtered_pseudo_normed_group_hom (rescale N (M ^ N)) M :=
∑ i, rescale_proj M N i

lemma sum_hom_apply (x) : sum_hom M N x = ∑ i, x i :=
comphaus_filtered_pseudo_normed_group_hom.sum_apply _ _ _

lemma sum_hom_strict [fact (0 < N)] : (sum_hom M N).strict :=
begin
  rw comphaus_filtered_pseudo_normed_group_hom.strict_iff_bound_by_one,
  have := comphaus_filtered_pseudo_normed_group_hom.sum_bound_by finset.univ
    (rescale_proj M N) (λ i, N⁻¹) (λ i _, rescale_proj_bound_by M N i),
  dsimp at this,
  simp only [finset.sum_const, finset.card_univ, fintype.card_fin, nsmul_eq_mul] at this,
  rwa [mul_inv_cancel] at this,
  apply ne_of_gt,
  norm_cast,
  exact fact.out _
end

end profinitely_filtered_pseudo_normed_group

namespace profinitely_filtered_pseudo_normed_group_with_Tinv

open profinitely_filtered_pseudo_normed_group

variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] [fact (0 < r')] [fact (0 < N)]

def sum_hom :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' (rescale N (M ^ N)) M :=
profinitely_filtered_pseudo_normed_group_with_Tinv_hom.mk'
  (sum_hom M N)
  (sum_hom_strict M N).bound_by_one
  (λ x, by { simp only [sum_hom, comphaus_filtered_pseudo_normed_group_hom.sum_apply,
    comphaus_filtered_pseudo_normed_group_hom.map_sum], refl })

include r'

lemma sum_hom_apply (x) : sum_hom M N x = ∑ i, x i :=
sum_hom_apply _ _ _

end profinitely_filtered_pseudo_normed_group_with_Tinv

end
