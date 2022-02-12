-- import laurent_measures.functor
import laurent_measures.thm69
-- import data.real.basic

/-
This files introduces the maps `Θ`, `Φ` and `Ψ` are the "measurifications" of `θ`, `ϕ` and `ψ` from
`laurent_measures.thm69`, they are morphisms in the right category.

We then prove in **???** that `θ_ϕ_exact` of `laurent_measures.thm69` becomes a short exact sequence
in the category **???**.
-/


noncomputable theory

namespace laurent_measures_ses

open nnreal laurent_measures pseudo_normed_group
open_locale big_operators nnreal

section homs

parameter {p : ℝ≥0}

def r : ℝ≥0 := (1 / 2) ^ (p:ℝ)

variables [fact(0 < p)] [fact (p < 1)]
variables [fact (0 < r)] --not nice, turn it into an instance
variable {S : Fintype}

local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

example : comphaus_filtered_pseudo_normed_group_with_Tinv r (ℒ S) :=
begin
  apply_instance,
end

example : comphaus_filtered_pseudo_normed_group (ℳ S) :=
begin
  -- constructor,
  -- intros c₁ c₂,
  exact real_measures.chpng_real_measures,
end

-- example : topological_space (S → ℝ) :=
-- begin
--   library_search
-- end

-- set_option trace.class_instances true --set_option trace.type_context.is_def_eq_detail true

example : topological_space (pseudo_normed_group.filtration(ℳ S) (1 : ℝ≥0)) :=
begin
  -- have := @subtype.topological_space ,
  apply @subtype.topological_space (S → ℝ) _ Pi.topological_space,
end

-- #help options

instance : comphaus_filtered_pseudo_normed_group_with_Tinv r (ℳ S) :=
{ topology := infer_instance,
  t2 := infer_instance,
  compact := infer_instance,
  continuous_add' :=  comphaus_filtered_pseudo_normed_group.continuous_add',
  continuous_neg' := comphaus_filtered_pseudo_normed_group.continuous_neg',
  continuous_cast_le := comphaus_filtered_pseudo_normed_group.continuous_cast_le,
  Tinv := begin
            fconstructor,
            intro f,
            use 2 • f,
            { exact smul_zero _ },
            { exact smul_add 2 },
            { use 2,
              rintros _ _ hf,
              rw [two_mul, two_smul],
              exact pseudo_normed_group.add_mem_filtration hf hf },
            { intros c₁ c₂ ϕ h,
              sorry,
              -- haveI : fact (c₁ ≤ c₂), sorry,
              -- let ψ : filtration (ℳ S) c₁ → filtration (ℳ S) (c₁ + c₁) := λ x, add' (x, x),
              -- have : ∀ x : (ℳ S), x ∈ filtration (ℳ S) c₁ → add' (x, x) ∈ filtration (ℳ S) (c₁ + c₁),
              -- simp_rw this at h,
              -- simp at h,


              -- rw ← two_mul at ψ,
              -- -- let ψ : filtration (ℳ S) c₁ → filtration (ℳ S) (c₁ + c₁) := λ x, x + x,
              -- simp_rw two_smul at h,
              -- have : ϕ = λ x, ((x + x) : pseudo_normed_group.filtration (ℳ S) c₂), sorry,


              -- have H : fact (c₁ ≤ c₂), sorry,
              -- have := @comphaus_filtered_pseudo_normed_group.continuous_cast_le (ℳ S) _ c₁ c₂ H,-- (ℳ S),
              -- sorry,
              -- use ℳ S,
              -- apply_instance,
              -- simp_rw two_smul at h,



            },
          end,
  Tinv_mem_filtration := sorry,
  ..(infer_instance : (comphaus_filtered_pseudo_normed_group (ℳ S))), }


  -- Tinv := sorry,
  -- Tinv_mem_filtration := sorry, }

-- instance chpng_real_measures : comphaus_filtered_pseudo_normed_group (ℳ p S) :=

-- instance [fact (0 < r)] : profinitely_filtered_pseudo_normed_group_with_Tinv r (ℳ S) :=
-- { to_add_comm_group := infer_instance,
  -- filtration := _,
  -- filtration_mono := _,
  -- zero_mem_filtration := _,
  -- neg_mem_filtration := _,
  -- add_mem_filtration := _,
  -- topology := _,
  -- t2 := _,
  -- compact := _,
  -- continuous_add' := _,
  -- continuous_neg' := _,
  -- continuous_cast_le := _,
  -- td := _,
  -- Tinv := _,
  -- Tinv_mem_filtration := _ }

-- begin

-- end

end homs

end laurent_measures_ses
