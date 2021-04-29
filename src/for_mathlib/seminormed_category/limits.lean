import data.real.basic
import for_mathlib.seminormed_category.basic
import category_theory.limits.has_limits
import for_mathlib.seminormed_category.functor

namespace category_theory

universes v u
variables {C : Type u} [category.{v} C] [semi_normed_category C]
variables {D : Type*} [category.{v} D] [semi_normed_category D] (G : C ⥤ D)
  [functor.bounded_additive G]
variables {J : Type v} [small_category J]

namespace limits

namespace cone

def bounded_by {F : J ⥤ C} (S : cone F) (c : ℝ) : Prop :=
∀ j : J, ∥ S.π.app j ∥ ≤ c

end cone

structure bounded_cone (F : J ⥤ C) :=
(cone : cone F)
(bounded : ∃ c, cone.bounded_by c)

namespace bounded_cone

noncomputable instance {F : J ⥤ C} : has_norm (bounded_cone F) := has_norm.mk $
λ S, Inf { a | S.cone.bounded_by a }

lemma norm_le {F : J ⥤ C} (S : bounded_cone F) (j : J) :
  ∥ S.cone.π.app j ∥ ≤ ∥ S ∥ := real.lb_le_Inf _ S.bounded (λ c hc, hc j)

lemma norm_nonneg {F : J ⥤ C} (S : bounded_cone F) : 0 ≤ ∥ S ∥ :=
begin
  by_cases h : nonempty J,
  { rcases h with ⟨j⟩,
    refine real.lb_le_Inf _ S.bounded (λ c hc, le_trans (norm_nonneg _) (hc j)) },
  suffices : ∥ S ∥ = 0, by simp [this],
  suffices : {a | S.cone.bounded_by a} = set.univ,
  { change Inf _ = _,
    simp [this, real.Inf_def, real.Sup_univ] },
  rw set.eq_univ_iff_forall,
  intros c j,
  exact false.elim (h ⟨j⟩),
end

end bounded_cone

end limits

namespace functor

def map_bounded_cone {F : J ⥤ C} (S : limits.bounded_cone F) :
  limits.bounded_cone (F ⋙ G) :=
{ cone := G.map_cone S.cone,
  bounded := begin
    use G.norm * ∥ S ∥,
    intros j,
    refine le_trans (G.le_norm _) _,
    have h : 0 ≤ G.norm := G.norm_nonneg,
    have h2 : ∥ S.cone.π.app j ∥ ≤ ∥ S ∥ := S.norm_le _,
    exact mul_le_mul_of_nonneg_left h2 h
  end }

end functor

end category_theory
