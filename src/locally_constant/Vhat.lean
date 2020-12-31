import topology.category.Profinite
import topology.algebra.group_completion
import topology.metric_space.completion

import locally_constant.NormedGroup
import locally_constant.for_mathlib
import normed_with_aut
import for_mathlib.functor

noncomputable theory

namespace NormedGroup
open uniform_space opposite

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

@[simps]
def incl {V : NormedGroup} : V ⟶ Completion.obj V :=
{ to_fun := λ v, (v : completion V),
  map_zero' := by simpa [completion.coe_eq],
  map_add' := completion.coe_add,
  bound' := ⟨1, λ v, by simp⟩ }

@[simp] lemma norm_incl_eq {V : NormedGroup} {v : V} : ∥incl v∥ = ∥v∥ := by simp

def Completion.lift {V W : NormedGroup} [complete_space W] (f : V ⟶ W) : Completion.obj V ⟶ W :=
{ to_fun := completion.extension f,
  map_zero' := begin
    erw completion.extension_coe,
    { simp },
    { exact normed_group_hom.uniform_continuous _ },
  end,
  map_add' := begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq _ _,
      { refine continuous.comp _ _,
        exact completion.continuous_extension,
        exact continuous_add },
      { refine continuous.add _ _,
        exact continuous.comp completion.continuous_extension continuous_fst,
        exact continuous.comp completion.continuous_extension continuous_snd } },
    { intros x y,
      rw ← completion.coe_add,
      repeat {rw completion.extension_coe},
      exact normed_group_hom.map_add _ _ _,
      all_goals {exact normed_group_hom.uniform_continuous _} }
  end,
  bound' := begin
    rcases f.bound with ⟨c,hc,h⟩,
    use c,
    intros v,
    apply completion.induction_on v; clear v,
    { refine is_closed_le _ _,
      refine continuous.comp continuous_norm completion.continuous_extension,
      refine continuous.mul continuous_const continuous_norm },
    { intros a,
      rw completion.extension_coe,
      { change _ ≤ c * ∥ incl _ ∥,
        simpa using h a },
      { exact normed_group_hom.uniform_continuous _ }}
  end }

lemma lift_comp_incl {V W : NormedGroup} [complete_space W] (f : V ⟶ W) : incl ≫ (Completion.lift f) = f :=
begin
  ext,
  change completion.extension f x = _,
  refine completion.extension_coe _ _,
  exact normed_group_hom.uniform_continuous _,
end

lemma lift_unique {V W : NormedGroup} [complete_space W] (f : V ⟶ W) (g : Completion.obj V ⟶ W) :
  incl ≫ g = f → g = Completion.lift f :=
begin
  intros h,
  ext,
  apply completion.induction_on x; clear x,
  { refine is_closed_eq _ _,
    exact g.continuous,
    exact normed_group_hom.continuous _ },
  { intros a,
    change (incl ≫ g) _ = (incl ≫ Completion.lift f) _,
    rw [lift_comp_incl, h] }
end

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

/-- `LCC` (Locally Constant Completion) is the bifunctor
that sends a normed abelian group `V` and a compact space `S` to `V-hat(S)`.
Here `V-hat(S)` is the completion (for the sup norm) of the locally constant functions `S → V`. -/
def LCC : NormedGroup ⥤ CompHausᵒᵖ ⥤ NormedGroup :=
(LocallyConstant.uncurry ⋙ Completion).curry

variables (S : Type*) [topological_space S] [compact_space S]

instance normed_with_aut_LocallyConstant (V : NormedGroup) (S : CompHaus) (r : ℝ)
  [normed_with_aut r V] [hr : fact (0 < r)] :
  normed_with_aut r ((LocallyConstant.obj V).obj (op S)) :=
{ T := (LocallyConstant.map_iso normed_with_aut.T).app (op S),
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

instance normed_with_aut_LCC (V : NormedGroup) (S : CompHaus) (r : ℝ)
  [normed_with_aut r V] [hr : fact (0 < r)] :
  normed_with_aut r ((LCC.obj V).obj (op S)) :=
show normed_with_aut r (Completion.obj $ (LocallyConstant.obj V).obj (op S)), by apply_instance

end NormedGroup
