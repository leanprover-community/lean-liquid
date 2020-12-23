import locally_constant.analysis
import NormedGroup

noncomputable theory

namespace NormedGroup

local attribute [instance] locally_constant.normed_group locally_constant.metric_space

@[simps]
def LocallyConstant (S : Type*) [topological_space S] [compact_space S] :
  NormedGroup ⥤ NormedGroup :=
{ obj := λ V, NormedGroup.of $ locally_constant S V,
  map := λ V W f,
  { to_fun := locally_constant.map f,
    continuous_to_fun := sorry, -- this is false if `f` is not bounded
    map_zero' := by { ext, exact f.map_zero' },
    map_add' := by { intros x y, ext s, apply f.map_add' } } }

end NormedGroup
