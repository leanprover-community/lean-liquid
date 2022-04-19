import laurent_measures.thm69

noncomputable theory

universe u

section add_stable


open laurent_measures theta pseudo_normed_group comphaus_filtered_pseudo_normed_group
-- open comphaus_filtered_pseudo_normed_group_hom
open_locale big_operators nnreal

parameter {p : ℝ≥0}
local notation `r` := @r p
local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r
variable [fact (0 < p)]
variable [fact (p < 1)]
variable [fact (0 < (1/2 : ℝ))]
variable [fact ((1/2 : ℝ) < 1)]

variable {S : Fintype.{u}}

local notation `ϖ` := Fintype.of (punit : Type u)

def θ_section (g : ℳ S) : (ℒ S) := ⟨ϑ_section (1 / 2 : ℝ) r p S g,
  summable_ϑ_section (1 / 2 : ℝ) r p S g⟩

-- instance : has_coe ℝ (ℳ S) := { coe := λ a s, a }

def real_add (a : ℝ) (F : ℒ S) : ℒ S := (θ_section (λ s, a)) + F

def add_real (F : ℒ S) (a : ℝ) : ℒ S := F + (θ_section (λ s, a))

lemma add_eq_add [fact (0 < (1/2 : ℝ))] [fact ((1/2 : ℝ) < 1)] (a : ℝ) (F : ℒ S) :
  real_add a F = add_real F a :=
begin
  dsimp [real_add, add_real],
  ext s n,
  simp only [one_div, add_apply],
  rw [add_comm _ (F s n)],
end



-- lemma summable_constant (a : ℝ) : summable (λ s,

-- instance : has_coe ℝ (ℒ S) :=
-- { coe := λ a (s : S) (n : ℤ), ⟨if n = 0 then a else 0,
-- begin

-- end⟩}

-- class is_add_stable (a : ℝ) (c : ℝ≥0) (X : set (filtration (ℒ S) c)) : Prop :=
-- (is_add_stable : ∀ F : filtration (ℒ S) c, F ∈ X → ∥ F.1 + a ∥ ≤ c)

end add_stable
