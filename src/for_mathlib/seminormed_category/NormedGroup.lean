import locally_constant.Vhat
import for_mathlib.seminormed_category.basic

open category_theory

namespace NormedGroup

noncomputable
instance : semi_normed_category NormedGroup :=
{ norm_comp' := λ P Q R f g, by {rw mul_comm, apply normed_group_hom.norm_comp_le} }

end NormedGroup
