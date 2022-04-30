import locally_constant.SemiNormedGroup
import normed_group.normed_with_aut
import analysis.normed.group.SemiNormedGroup.completion

/-!

# Completions of normed groups

This file contains an API for completions for seminormed groups equipped with
an automorphism which scales norms by a constant factor `r`.

## Main definitions

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

open uniform_space _root_.opposite _root_.category_theory Completion

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
  exact (Completion.map_norm_noninc $ LocallyConstant_obj_map_norm_noninc _ _ _ _)
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
