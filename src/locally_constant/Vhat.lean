import category_theory.currying
import category_theory.preadditive.additive_functor
import topology.category.Profinite
import topology.algebra.normed_group
import topology.algebra.group_completion
import topology.metric_space.completion

import for_mathlib.normed_group

import locally_constant.SemiNormedGroup
import normed_group.normed_with_aut

/-

# Completions of normed groups

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms), and also a variant: completions for seminormed groups equipped with
an automorphism which scales norms by a constant factor `r`.

## Main definitions

- `Completion` : the completion of a seminormed group (defined as a functor on `SemiNormedGroup`)
- `Completion.lift` : a normed group hom from `V` to complete `W` extends ("lifts")
  to a seminormed group from the completion of `V` to `W`.
- `normed_with_aut_Completion` : if `V` is equipped with an automorphism changing norms
  by a factor `r` then the completion also has such an automorphism.
- `LCC : SemiNormedGroup ⥤ Profiniteᵒᵖ ⥤ SemiNormedGroup` :
  `LCC V S` is the seminormed group completion of the locally constant functions from `S` to `V`.

## TODO

Pull off the stuff about completions and put it into `normed_group/SemiNormedGroup`?
Then `system_of_complexes.basic` would not have to import this file.

-/

noncomputable theory
open_locale nnreal

universe u

namespace SemiNormedGroup
open uniform_space opposite category_theory

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGroup`. -/
@[simps]
def Completion : SemiNormedGroup.{u} ⥤ SemiNormedGroup.{u} :=
{ obj := λ V, SemiNormedGroup.of (completion V),
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

instance Completion_complete_space {V : SemiNormedGroup} : complete_space (Completion.obj V) :=
begin
  change complete_space (completion V),
  apply_instance
end

/-- The canonical morphism from a seminormed group `V` to its completion. -/
@[simps]
def incl {V : SemiNormedGroup} : V ⟶ Completion.obj V :=
{ to_fun := λ v, (v : completion V),
  map_add' := completion.coe_add,
  bound' := ⟨1, λ v, by simp⟩ }

@[simp] lemma norm_incl_eq {V : SemiNormedGroup} {v : V} : ∥incl v∥ = ∥v∥ := by simp

lemma Completion_map_bound_by {V W : SemiNormedGroup} (f : V ⟶ W) (C : ℝ≥0) (hf : f.bound_by C) :
  (Completion.map f).bound_by C :=
begin
  intros v,
  apply completion.induction_on v; clear v,
  { exact is_closed_le (continuous_norm.comp completion.continuous_map)
      (continuous_const.mul continuous_norm), },
  intro v,
  simp only [completion.norm_coe, Completion_map_apply, completion.map_coe f.uniform_continuous],
  exact hf v
end

lemma Completion_map_norm_noninc {V W : SemiNormedGroup} (f : V ⟶ W) (hf : f.norm_noninc) :
  (Completion.map f).norm_noninc :=
begin
  intros v,
  apply completion.induction_on v; clear v,
  { refine is_closed_le (continuous_norm.comp completion.continuous_map) continuous_norm },
  intro v,
  simp only [completion.norm_coe, Completion_map_apply, completion.map_coe f.uniform_continuous],
  exact hf v
end

/--
Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive.
-/
def Completion.map_hom (V W : SemiNormedGroup.{u}) : (V ⟶ W) →+ (Completion.obj V ⟶ Completion.obj W) :=
add_monoid_hom.mk' (category_theory.functor.map Completion) $
begin
  intros f g, ext v,
  apply uniform_space.completion.induction_on v,
  { refine is_closed_eq (normed_group_hom.continuous _) _,
    apply continuous.add; apply normed_group_hom.continuous },
  { clear v, intro v,
    simp only [normed_group_hom.coe_add, pi.add_apply,
      Completion_map_apply, normed_group_hom.coe_add],
    rw [uniform_space.completion.map_coe,
        uniform_space.completion.map_coe f.uniform_continuous,
        uniform_space.completion.map_coe g.uniform_continuous],
    { rw [pi.add_apply, uniform_space.completion.coe_add] },
    { exact (f + g).uniform_continuous } }
end


@[simp] lemma Completion.map_zero (V W : SemiNormedGroup) : Completion.map (0 : V ⟶ W) = 0 :=
(Completion.map_hom V W).map_zero

instance : preadditive SemiNormedGroup.{u} :=
{ hom_group := λ P Q, infer_instance,
  add_comp' := by { intros, ext,
    simp only [normed_group_hom.add_apply, comp_apply, normed_group_hom.map_add], },
  comp_add' := by { intros, ext,
    simp only [normed_group_hom.add_apply, comp_apply, normed_group_hom.map_add], } }

instance : functor.additive Completion :=
{ map_zero' := Completion.map_zero,
  map_add' := λ X Y, (Completion.map_hom _ _).map_add }

/--
Given a normed group hom `f : V → W` with `W` complete, this provides a lift of `f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the api for the
universal property of the completion.
-/
def Completion.lift {V W : SemiNormedGroup} [complete_space W]
  [t2_space W] [separated_space W] -- these should be redundant
  (f : V ⟶ W) : Completion.obj V ⟶ W :=
{ to_fun := completion.extension f,
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
      { change _ ≤ ↑c * ∥incl _∥,
        simpa using h a },
      { exact normed_group_hom.uniform_continuous _ }}
  end }

lemma lift_comp_incl {V W : SemiNormedGroup} [complete_space W]
  [t2_space W] [separated_space W] -- these should be redundant
  (f : V ⟶ W) : incl ≫ (Completion.lift f) = f :=
begin
  ext,
  change completion.extension f x = _,
  refine completion.extension_coe _ _,
  exact normed_group_hom.uniform_continuous _,
end

lemma lift_unique {V W : SemiNormedGroup} [complete_space W]
  [t2_space W] [separated_space W] -- these should be redundant
  (f : V ⟶ W) (g : Completion.obj V ⟶ W) :
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

instance normed_with_aut_Completion (V : SemiNormedGroup.{u}) (r : ℝ≥0) [normed_with_aut r V] :
  normed_with_aut r (Completion.obj V) :=
{ T := Completion.map_iso normed_with_aut.T,
  norm_T :=
  begin
    rw ← function.funext_iff,
    refine abstract_completion.funext completion.cpkg _ _ _,
    { apply continuous_norm.comp _, exact completion.continuous_map },
    { exact (continuous_const.mul continuous_norm : _) },
    intro v,
    calc _ = _ : congr_arg norm (completion.map_coe _ _)
       ... = _ : _,
    { exact normed_group_hom.uniform_continuous _ },
    { erw [completion.norm_coe, normed_with_aut.norm_T, completion.norm_coe] }
  end }

@[simp] lemma Completion_T_inv_eq (V : SemiNormedGroup.{u}) (r : ℝ≥0) [normed_with_aut r V] :
  (normed_with_aut.T.hom : Completion.obj V ⟶ _) = Completion.map normed_with_aut.T.hom := rfl

lemma T_hom_incl {V : SemiNormedGroup} {r : ℝ≥0} [normed_with_aut r V] :
  (incl : V ⟶ _) ≫ normed_with_aut.T.hom = normed_with_aut.T.hom ≫ incl :=
begin
  ext x,
  simp only [incl_apply, category_theory.comp_apply, Completion_T_inv_eq],
  change completion.map normed_with_aut.T.hom _ = _,
  rw completion.map_coe,
  exact normed_group_hom.uniform_continuous _,
end

lemma T_hom_eq {V : SemiNormedGroup} {r : ℝ≥0} [normed_with_aut r V] :
  normed_with_aut.T.hom = Completion.lift ((normed_with_aut.T.hom : V ⟶ V) ≫ incl) :=
lift_unique _ _ T_hom_incl

/-- `LCC` (Locally Constant Completion) is the bifunctor
that sends a seminormed group `V` and a profinite space `S` to `V-hat(S)`.
Here `V-hat(S)` is the completion (for the sup norm) of the locally constant functions `S → V`. -/
def LCC : SemiNormedGroup ⥤ Profiniteᵒᵖ ⥤ SemiNormedGroup :=
curry.obj ((uncurry.obj LocallyConstant) ⋙ Completion)

lemma LCC_obj_map' (V : SemiNormedGroup) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X) :
  (LCC.obj V).map f = Completion.map ((LocallyConstant.obj V).map f) :=
begin
  delta LCC,
  simp only [curry.obj_obj_map, LocallyConstant_obj_map, functor.comp_map, uncurry.obj_map,
    nat_trans.id_app, functor.map_comp, functor.map_id, category_theory.functor.map_id],
  erw [← functor.map_comp, category.id_comp]
end

lemma LCC_obj_map (V : SemiNormedGroup) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X) (v : (LCC.obj V).obj Y) :
  (LCC.obj V).map f v = completion.map (locally_constant.comap f.unop) v :=
by { rw LCC_obj_map', refl }

lemma LCC_obj_map_norm_noninc (V : SemiNormedGroup) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X) :
  ((LCC.obj V).map f).norm_noninc :=
begin
  rw LCC_obj_map',
  exact (Completion_map_norm_noninc _ $ LocallyConstant_obj_map_norm_noninc _ _ _ _)
end

variables (S : Type*) [topological_space S] [compact_space S]

@[simps]
instance normed_with_aut_LocallyConstant (V : SemiNormedGroup) (S : Profiniteᵒᵖ) (r : ℝ≥0)
  [normed_with_aut r V] [hr : fact (0 < r)] :
  normed_with_aut r ((LocallyConstant.obj V).obj S) :=
{ T := (LocallyConstant.map_iso normed_with_aut.T).app S,
  norm_T :=
  begin
    rw ← op_unop S,
    rintro (f : locally_constant (unop S : Profinite) V),
    show Sup _ = ↑r * Sup _,
    dsimp,
    simp only [normed_with_aut.norm_T],
    convert real.Sup_mul r _ hr.out,
    ext,
    simp only [exists_prop, set.mem_range, exists_exists_eq_and, set.mem_set_of_eq]
  end }

instance normed_with_aut_LCC (V : SemiNormedGroup) (S : Profiniteᵒᵖ) (r : ℝ≥0)
  [normed_with_aut r V] [hr : fact (0 < r)] :
  normed_with_aut r ((LCC.obj V).obj S) :=
show normed_with_aut r (Completion.obj $ (LocallyConstant.obj V).obj S), by apply_instance

end SemiNormedGroup

#lint- only unused_arguments def_lemma doc_blame
