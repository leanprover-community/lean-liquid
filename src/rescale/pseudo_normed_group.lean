import pseudo_normed_group.category
import rescale.basic

noncomputable theory

open_locale nnreal

namespace rescale

open pseudo_normed_group

variables (r r' : ℝ≥0) (M : Type*)

section pseudo_normed_group

variables [pseudo_normed_group M]

instance : pseudo_normed_group (rescale r M) :=
{ filtration := λ c, show set M, from filtration M (c * r⁻¹),
  filtration_mono := λ c₁ c₂ h, filtration_mono (mul_le_mul' h le_rfl),
  zero_mem_filtration := λ c, @zero_mem_filtration M _ _,
  neg_mem_filtration := λ c, @neg_mem_filtration M _ _,
  add_mem_filtration := λ c₁ c₂, by { simp only [add_mul], apply add_mem_filtration } }

lemma mem_filtration (x : rescale r M) (c : ℝ≥0) :
  x ∈ filtration (rescale r M) c ↔ (of.symm x) ∈ filtration M (c * r⁻¹) :=
iff.rfl

lemma mem_filtration' (x : rescale r M) (c : ℝ≥0) [fact (0 < r)] :
of x ∈ filtration (rescale r M) c ↔ x ∈ filtration M (c * r⁻¹) := iff.rfl

def to_rescale_one_strict_pseudo_normed_group_hom :
strict_pseudo_normed_group_hom M (rescale 1 M) :=
{ to_fun := rescale.of,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  strict' := λ c x hx, by rwa [mem_filtration', inv_one, mul_one]
}

def of_rescale_one_strict_pseudo_normed_group_hom :
strict_pseudo_normed_group_hom (rescale 1 M) M :=
{ to_fun := rescale.of.symm,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  strict' := λ c x hx, by rwa [mem_filtration, inv_one, mul_one] at hx
}

def of_to_rescale_one_comp_eq_id [fact (0 < r)] [fact (0 < r')] :
  (of_rescale_one_strict_pseudo_normed_group_hom M).comp
  (to_rescale_one_strict_pseudo_normed_group_hom M) =
  strict_pseudo_normed_group_hom.id (rescale 1 M) :=
rfl

def to_of_rescale_one_comp_eq_id [fact (0 < r)] [fact (0 < r')] :
  (to_rescale_one_strict_pseudo_normed_group_hom M).comp
  (of_rescale_one_strict_pseudo_normed_group_hom M) =
  strict_pseudo_normed_group_hom.id M :=
rfl

def of_rescale_rescale_strict_pseudo_normed_group_hom [fact (0 < r)] [fact (0 < r')]:
strict_pseudo_normed_group_hom (rescale r (rescale r' M)) (rescale (r' * r) M) :=
{ to_fun := λ m, (rescale.of (rescale.of.symm (rescale.of.symm m))),
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  strict' := λ c x hx, begin
    rwa [mem_filtration', nnreal.mul_inv, ← mul_assoc, ← mem_filtration r' M, ← mem_filtration r],
  end }

def to_rescale_rescale_strict_pseudo_normed_group_hom [fact (0 < r)] [fact (0 < r')]:
strict_pseudo_normed_group_hom (rescale (r' * r) M) (rescale r (rescale r' M)) :=
{ to_fun := λ m, (rescale.of (rescale.of (rescale.of.symm m))),
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  strict' := λ c x hx, begin
    rwa [mem_filtration' r (rescale r' M), mem_filtration' r' M, mul_assoc, ← nnreal.mul_inv,
      ← mem_filtration (r' * r) M],
  end }

def of_to_rescale_rescale_comp_eq_id [fact (0 < r)] [fact (0 < r')] :
  (of_rescale_rescale_strict_pseudo_normed_group_hom r r' M).comp
  (to_rescale_rescale_strict_pseudo_normed_group_hom r r' M) =
  strict_pseudo_normed_group_hom.id (rescale r (rescale r' M)) :=
rfl

def to_of_rescale_rescale_comp_eq_id' [fact (0 < r)] [fact (0 < r')] :
  (to_rescale_rescale_strict_pseudo_normed_group_hom r r' M).comp
  (of_rescale_rescale_strict_pseudo_normed_group_hom r r' M) =
  strict_pseudo_normed_group_hom.id (rescale (r' * r) M) :=
rfl

end pseudo_normed_group


--Should we change name to this section? But one for the comphaus_fil.. and one for the
--profinitely_filt.. seems a lot
section profinitely_filtered_pseudo_normed_group

open comphaus_filtered_pseudo_normed_group profinitely_filtered_pseudo_normed_group

instance [comphaus_filtered_pseudo_normed_group M] :
  comphaus_filtered_pseudo_normed_group (rescale r M) :=
{ topology := by { delta rescale, apply_instance },
  t2 := by { delta rescale, apply_instance },
  compact := by { delta rescale, apply_instance },
  continuous_add' :=
  begin
    intros c₁ c₂,
    haveI : fact ((c₁ + c₂) * r⁻¹ ≤ c₁ * r⁻¹ + c₂ * r⁻¹) := ⟨(add_mul _ _ _).le⟩,
    rw (embedding_cast_le ((c₁ + c₂) * r⁻¹) (c₁ * r⁻¹ + c₂ * r⁻¹)).continuous_iff,
    exact (continuous_add' (c₁ * r⁻¹) (c₂ * r⁻¹)),
  end,
  continuous_neg' := λ c, continuous_neg' _,
  continuous_cast_le := λ c₁ c₂ h, by exactI continuous_cast_le _ _,}

instance [profinitely_filtered_pseudo_normed_group M] :
  profinitely_filtered_pseudo_normed_group (rescale r M) := {}

@[simps]
def map_comphaus_filtered_pseudo_normed_group_hom {M₁ M₂ : Type*}
  [comphaus_filtered_pseudo_normed_group M₁] [comphaus_filtered_pseudo_normed_group M₂]
  (N : ℝ≥0) (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  comphaus_filtered_pseudo_normed_group_hom (rescale N M₁) (rescale N M₂) :=
{ to_fun := rescale.of ∘ f ∘ rescale.of.symm,
  map_zero' := f.map_zero,
  map_add' := λ x y, f.map_add x y,
  bound' := begin
    obtain ⟨C, hC⟩ := f.bound,
    refine ⟨C, λ c x hx, _⟩,
    rw rescale.mem_filtration at hx ⊢,
    simp only [function.comp_app, equiv.symm_apply_apply, mul_assoc],
    exact hC hx,
  end,
  continuous' := λ c₁ c₂ f₀ hf₀, f.continuous f₀ hf₀, }

@[simps]
def map_strict_comphaus_filtered_pseudo_normed_group_hom {M₁ M₂ : Type*}
  [comphaus_filtered_pseudo_normed_group M₁] [comphaus_filtered_pseudo_normed_group M₂]
  (N : ℝ≥0) (f : strict_comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  strict_comphaus_filtered_pseudo_normed_group_hom (rescale N M₁) (rescale N M₂) :=
{ to_fun := rescale.of ∘ f ∘ rescale.of.symm,
  map_zero' := f.map_zero,
  map_add' := λ x y, f.map_add x y,
  strict' := λ c x hx, begin
    rw rescale.mem_filtration at hx ⊢,
    simp only [function.comp_app, equiv.symm_apply_apply, mul_assoc],
    exact f.strict hx,
  end,
  continuous' := λ c, f.continuous' _, }

end profinitely_filtered_pseudo_normed_group

section profinitely_filtered_pseudo_normed_group_with_Tinv

open profinitely_filtered_pseudo_normed_group_with_Tinv
open profinitely_filtered_pseudo_normed_group

variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]

include r'

@[simps]
def Tinv' : rescale r M →+ rescale r M :=
{ to_fun := λ x, of $ Tinv $ of.symm x,
  map_zero' := by { delta rescale, exact Tinv.map_zero },
  map_add' := by { delta rescale, exact Tinv.map_add } }

lemma Tinv'_mem_filtration (c : ℝ≥0) (x : rescale r M) (hx : x ∈ filtration (rescale r M) c) :
  (Tinv' r r' M) x ∈ filtration (rescale r M) (r'⁻¹ * c) :=
by simpa only [mem_filtration, Tinv'_apply, equiv.symm_apply_apply, mul_assoc]
  using Tinv_mem_filtration _ _ hx

variable [fact (0 < r')]

@[simps]
def Tinv : comphaus_filtered_pseudo_normed_group_hom (rescale r M) (rescale r M) :=
comphaus_filtered_pseudo_normed_group_hom.mk' (Tinv' r r' M)
begin
  refine ⟨r'⁻¹, λ c, ⟨Tinv'_mem_filtration r r' M c, _⟩⟩,
  haveI :  fact (c * r⁻¹ ≤ r' * (r'⁻¹ * c * r⁻¹)) :=
    ⟨by rw [mul_assoc, mul_inv_cancel_left₀ ‹fact (0 < r')›.1.ne.symm]⟩,
  apply Tinv₀_continuous,
end

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (rescale r M) :=
{ Tinv := rescale.Tinv r r' M,
  Tinv_mem_filtration := Tinv'_mem_filtration r r' M,
  .. rescale.profinitely_filtered_pseudo_normed_group r M }

@[simps]
def map_comphaus_filtered_pseudo_normed_group_with_Tinv_hom {M₁ M₂ : Type*}
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₁]
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₂]
  (N : ℝ≥0) (f : comphaus_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂) :
  comphaus_filtered_pseudo_normed_group_with_Tinv_hom r' (rescale N M₁) (rescale N M₂) :=
{ to_fun := rescale.of ∘ f ∘ rescale.of.symm,
  strict' := λ c x hx, begin
    rw rescale.mem_filtration at hx ⊢,
    simp only [function.comp_app, equiv.symm_apply_apply, mul_assoc],
    exact f.strict hx,
  end,
  map_Tinv' := f.map_Tinv,
  continuous' := λ c, f.continuous' (c * N⁻¹),
  .. map_comphaus_filtered_pseudo_normed_group_hom N
      f.to_comphaus_filtered_pseudo_normed_group_hom }

end profinitely_filtered_pseudo_normed_group_with_Tinv

end rescale

namespace ProFiltPseuNormGrpWithTinv

variables (r' : ℝ≥0) [fact (0 < r')]

@[simps]
def rescale (N : ℝ≥0) : ProFiltPseuNormGrpWithTinv r' ⥤ ProFiltPseuNormGrpWithTinv r' :=
{ obj := λ M, of r' $ rescale N M,
  map := λ M₁ M₂ f, rescale.map_comphaus_filtered_pseudo_normed_group_with_Tinv_hom _ _ f }

end ProFiltPseuNormGrpWithTinv

namespace ProFiltPseuNormGrpWithTinv₁

variables (r' : ℝ≥0) [fact (0 < r')]

@[simps]
def rescale (N : ℝ≥0) [fact (0 < N)] :
  ProFiltPseuNormGrpWithTinv₁ r' ⥤ ProFiltPseuNormGrpWithTinv₁ r' :=
{ obj := λ M,
  { M := rescale N M,
    exhaustive' := λ x,
    begin
      obtain ⟨c, hc⟩ := M.exhaustive r' (rescale.of.symm x),
      refine ⟨c * N, _⟩,
      rw rescale.mem_filtration,
      rwa mul_inv_cancel_right₀,
      exact (fact.out _ : 0 < N).ne'
    end },
  map := λ M₁ M₂ f, rescale.map_comphaus_filtered_pseudo_normed_group_with_Tinv_hom _ _ f, }
.

@[simps]
def rescale_out (N : ℝ≥0) [fact (1 ≤ N)] :
  rescale r' N ⟶ 𝟭 _ :=
{ app := λ M,
  { to_fun := (rescale.of.symm : _root_.rescale N M → M),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    strict' := λ c x hx, pseudo_normed_group.filtration_mono (fact.out _) hx,
    continuous' := λ c, comphaus_filtered_pseudo_normed_group.continuous_cast_le (c * N⁻¹) c,
    map_Tinv' := λ x, rfl } }

end ProFiltPseuNormGrpWithTinv₁
