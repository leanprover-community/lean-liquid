import category_theory.currying
import category_theory.preadditive.additive_functor
import topology.category.Profinite
import topology.algebra.normed_group
import topology.algebra.group_completion
import topology.metric_space.completion

import for_mathlib.normed_group_hom_completion

import locally_constant.SemiNormedGroup

/-

# Completions of normed groups

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms), and also a variant: completions for seminormed groups equipped with
an automorphism which scales norms by a constant factor `r`.

## Main definitions

- `Completion` : the completion of a seminormed group (defined as a functor on `SemiNormedGroup`)
- `Completion.lift` : a normed group hom from `V` to complete `W` extends ("lifts")
  to a seminormed group from the completion of `V` to `W`.

-/

noncomputable theory

universe u

namespace SemiNormedGroup
open uniform_space opposite category_theory

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGroup`. -/
@[simps]
def Completion : SemiNormedGroup.{u} ⥤ SemiNormedGroup.{u} :=
{ obj := λ V, SemiNormedGroup.of (completion V),
  map := λ V W f, normed_group_hom.completion f,
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

lemma Completion_map_norm_noninc {V W : SemiNormedGroup} (f : V ⟶ W) (hf : f.norm_noninc) :
  (Completion.map f).norm_noninc :=
normed_group_hom.norm_noninc_iff_norm_le_one.2 $ le_trans
  (normed_group_hom.norm_completion_le f) $ normed_group_hom.norm_noninc_iff_norm_le_one.1 hf

/--
Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive.
-/
def Completion.map_hom (V W : SemiNormedGroup.{u}) : (V ⟶ W) →+ (Completion.obj V ⟶ Completion.obj W) :=
add_monoid_hom.mk' (category_theory.functor.map Completion) $ λ f g,
  normed_group_hom.completion_add f g


@[simp] lemma Completion.map_zero (V W : SemiNormedGroup) : Completion.map (0 : V ⟶ W) = 0 :=
(Completion.map_hom V W).map_zero

instance : preadditive SemiNormedGroup.{u} :=
{ hom_group := λ P Q, infer_instance,
  add_comp' := by { intros, ext,
    simp only [normed_group_hom.add_apply, category_theory.comp_apply, normed_group_hom.map_add] },
  comp_add' := by { intros, ext,
    simp only [normed_group_hom.add_apply, category_theory.comp_apply, normed_group_hom.map_add] } }

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
      { change _ ≤ c * ∥incl _∥,
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

end SemiNormedGroup
