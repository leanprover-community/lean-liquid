import algebra.group.ulift
import for_mathlib.SemiNormedGroup

universes v u

namespace pseudo_metric_space

variables (V : Type u) [pseudo_metric_space V]

instance : pseudo_metric_space (ulift.{v} V) :=
sorry

end pseudo_metric_space

namespace semi_normed_group

variables (V : Type u) [semi_normed_group V]

instance : semi_normed_group (ulift.{v} V) :=
{ norm := sorry,
  dist_eq := sorry,
  .. (by apply_instance : pseudo_metric_space (ulift.{v} V)),
  .. (by apply_instance : add_comm_group (ulift.{v} V)) }

end semi_normed_group

namespace SemiNormedGroup

def ulift : SemiNormedGroup.{u} ⥤ SemiNormedGroup.{max u v} :=
{ obj := λ V, of (ulift.{v} V),
  map := λ V W f, sorry,
  map_id' := sorry,
  map_comp' := sorry }

end SemiNormedGroup
