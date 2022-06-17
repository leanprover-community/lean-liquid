import algebra.category.Group.colimits
import category_theory.limits.has_limits
import group_theory.torsion

noncomputable theory
variables {G : Type} [comm_group G]

open category_theory monoid category_theory.limits

def index_category_of_torsion_free (hG : is_torsion_free G) : Cat := sorry

def index_functor_of_torsion_free (hG : is_torsion_free G) :
  (index_category_of_torsion_free hG) ⥤ CommGroup := sorry

instance index_concrete [hG : is_torsion_free G] : concrete_category (index_category_of_torsion_free hG) := sorry

instance has_colimit_of_torsion_free [hG : is_torsion_free G] : has_colimit (index_functor_of_torsion_free hG) := sorry

-- lemma colimit_of_torsion_free (hG : is_torsion_free G) : G ≃ colimit(index_functor_of_torsion_free hG) := sorry
