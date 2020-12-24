import topology.category.Profinite
import topology.algebra.group_completion
import topology.metric_space.completion

import locally_constant.NormedGroup
import locally_constant.for_mathlib
import normed_with_aut

noncomputable theory

namespace NormedGroup
open uniform_space

def Completion : NormedGroup ⥤ NormedGroup :=
{ obj := λ V, NormedGroup.of (completion V),
  map := λ V W f,
  { to_fun := completion.map f,
    bound' :=
    begin
      obtain ⟨C, C_pos, hC⟩ := f.bound,
      use C,
      intro v,
      apply completion.induction_on v; clear v,
      { refine is_closed_le _ _,
        { exact continuous_norm.comp completion.continuous_map },
        { exact continuous_const.mul continuous_norm } },
      { intro v,
        rw [completion.map_coe, completion.norm_coe, completion.norm_coe],
        { apply hC },
        { exact f.uniform_continuous } }
    end,
    map_zero' := by { erw [completion.map_coe], { congr' 1, exact f.map_zero' },
      exact normed_group_hom.uniform_continuous f },
    map_add' :=
    begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq _ _,
      { exact completion.continuous_map.comp continuous_add },
      { apply continuous.add,
        { exact completion.continuous_map.comp continuous_fst },
        { exact completion.continuous_map.comp continuous_snd } } },
    { intros x y,
      rw [← completion.coe_add, completion.map_coe,
        completion.map_coe, completion.map_coe, ← completion.coe_add],
      { congr' 1, exact f.map_add' x y },
      all_goals { exact normed_group_hom.uniform_continuous f } }
    end },
  map_id' := λ V, by { ext1 v, show completion.map id v = v, rw completion.map_id, refl },
  map_comp' :=
  begin
    intros U V W f g, ext1 v, show completion.map (g ∘ f) v = _, rw ← completion.map_comp,
    { refl },
    { exact normed_group_hom.uniform_continuous _ },
    { exact normed_group_hom.uniform_continuous _ }
  end }

instance normed_with_aut_Completion (V : NormedGroup) (r : ℝ) [normed_with_aut r V] :
  normed_with_aut r (Completion.obj V) :=
{ T := Completion.map_iso normed_with_aut.T,
  norm_T :=
  begin
    rw ← function.funext_iff,
    refine abstract_completion.funext completion.cpkg _ _ _,
    { apply continuous_norm.comp _, exact completion.continuous_map },
    { apply continuous_const.mul continuous_norm },
    intro v,
    calc _ = _ : congr_arg norm (completion.map_coe _ _)
       ... = _ : _,
    { exact normed_group_hom.uniform_continuous _ },
    { erw [completion.norm_coe, normed_with_aut.norm_T, completion.norm_coe] }
  end }

/-- The functor that sends `V` to `V-hat(S)`, for a given compact space `S`. -/
def LCC (S : Type*) [topological_space S] [compact_space S] :
  NormedGroup ⥤ NormedGroup :=
NormedGroup.LocallyConstant S ⋙ NormedGroup.Completion

variables (S : Type*) [topological_space S] [compact_space S]

instance normed_with_aut_LocallyConstant (V : NormedGroup) (r : ℝ)
  [normed_with_aut r V] [hr : fact (0 < r)] :
  normed_with_aut r ((LocallyConstant S).obj V) :=
{ T := (LocallyConstant S).map_iso normed_with_aut.T,
  norm_T :=
  begin
    rintro (f : locally_constant S V),
    show Sup _ = r * Sup _,
    dsimp,
    simp only [normed_with_aut.norm_T],
    convert real.Sup_mul r _ hr,
    ext,
    simp only [exists_prop, set.mem_range, exists_exists_eq_and, set.mem_set_of_eq]
  end }

instance normed_with_aut_LCC (V : NormedGroup) (r : ℝ) [normed_with_aut r V] [hr : fact (0 < r)] :
  normed_with_aut r ((LCC S).obj V) :=
show normed_with_aut r (Completion.obj $ (LocallyConstant S).obj V), by apply_instance

-- def comap (f : S₁ → S₂) : hat S₂ V → hat S₁ V :=
-- completion.map $ locally_constant.comap f

end NormedGroup
