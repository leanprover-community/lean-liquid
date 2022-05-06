import algebra.category.Group.abelian
import topology.continuous_function.compact
import analysis.normed.group.SemiNormedGroup.completion

noncomputable theory

universes u

open category_theory opposite

variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

-- move me
instance SemiNormedGroup.forget₂ : has_forget₂ SemiNormedGroup.{u} Ab.{u} :=
{ forget₂ :=
  { obj := λ V, AddCommGroup.of V,
    map := λ V W f, f.to_add_monoid_hom,
    map_id' := λ V, rfl,
    map_comp' := λ _ _ _ f g, rfl },
  forget_comp := rfl }

-- move me
instance SemiNormedGroup.forget₂_additive :
  (forget₂ SemiNormedGroup.{u} Ab.{u}).additive :=
{ map_add' := by { intros, refl } }

instance SemiNormedGroup.metric_space : metric_space V :=
metric.of_t2_pseudo_metric_space ‹_›

instance SemiNormedGroup.normed_group : normed_group V :=
{ dist_eq := semi_normed_group.dist_eq,
  ..(by apply_instance : semi_normed_group V) }
