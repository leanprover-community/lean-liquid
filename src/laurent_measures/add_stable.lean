import laurent_measures.thm69

noncomputable theory

section add_stable


open laurent_measures theta pseudo_normed_group comphaus_filtered_pseudo_normed_group
-- open comphaus_filtered_pseudo_normed_group_hom
open_locale big_operators nnreal

parameter {p : ℝ≥0}
local notation `r` := @r p
local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r
local notation `ϖ` := Fintype.of unit

variable {S : Fintype.{0}}

instance : has_coe ℝ (ℳ S) := {coe := λ a s, a }

variable [fact (0 < p)]
variable [fact (p < 1)]
instance one_half_pos' : fact (0 < (1/2 : ℝ)) := ⟨one_half_pos⟩
instance one_half_lt_one' : fact ((1/2 : ℝ) < 1) := ⟨one_half_lt_one⟩


def θ_section (g : ℳ S) : (ℒ S) := ⟨ϑ_section (1 / 2 : ℝ) r p S g,
  summable_ϑ_section (1 / 2 : ℝ) r p S g⟩


def real_add (a : ℝ) (F : ℒ S) : ℒ S := (θ_section a) + F

def add_real (F : ℒ S) (a : ℝ) : ℒ S := F + (θ_section a)

lemma add_eq_add [fact (0 < (1/2 : ℝ))] [fact ((1/2 : ℝ) < 1)] (a : ℝ) (F : ℒ S) :
  real_add a F = add_real F a :=
begin
  dsimp [real_add, add_real],
  ext s n,
  simp only [one_div, add_apply],
  rw [add_comm _ (F s n)],
end

class add_stable (a : ℝ) (c : ℝ≥0) (X : set (ℒ S)) : Prop :=
(is_add_stable : ∀ F : filtration (ℒ S) c, F.1 ∈ X → (real_add a F.1) ∈ X)

-- class add_stable' (a : ℝ) (c : ℝ≥0) (X : set (filtration (ℒ S) c)) : Prop :=
-- (is_add_bdd'    : ∀ F : filtration (ℒ S) c, F ∈ X → ∥ real_add a F.1 ∥ ≤ c)
-- (is_add_stable' : ∀ F : filtration (ℒ S) c, F ∈ X →
--   (mem_filtration_iff (real_add a F.1) c).mpr (is_add_bdd' F _))

lemma is_add_stable_iff_swap (a : ℝ) (c : ℝ≥0) (X : set (ℒ S)) : (add_stable a c X) ↔
  (∀ F : filtration (ℒ S) c, F.1 ∈ X → (add_real F.1 a) ∈ X) := --by {simpa using [add_eq_add]}
begin
  split,
  { intros hX F hF,
    cases hX,
    specialize hX F hF,
    rwa add_eq_add at hX },
  { intro hX,
    constructor,
    intros F hF,
    specialize hX F hF,
    rwa [← add_eq_add] at hX },
end

-- lemma level_closed (a : ℝ) (c c' : ℝ≥0) (H : c ≤ c') (X : set (ℒ S)) (hX : add_stable a c X) :
--  is_closed (X

end add_stable
