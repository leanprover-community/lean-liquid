import data.real.basic
import for_mathlib.seminormed_category.basic
import category_theory.limits.has_limits
import for_mathlib.seminormed_category.functor

namespace category_theory

universes v u
variables {C : Type u} [category.{v} C] [semi_normed_category C]
variables {D : Type*} [category.{v} D] [semi_normed_category D] (G : C ⥤ D)
  [functor.norm_compat G]
variables {J : Type v} [small_category J]

namespace limits

structure bounded_cone (F : J ⥤ C) :=
(cone : cone F)
[bounded : nat_trans.bounded cone.π]

instance {F : J ⥤ C} {s : bounded_cone F} : nat_trans.bounded s.cone.π := s.bounded

structure bounded_cocone (F : J ⥤ C) :=
(cocone : cocone F)
[bounded : nat_trans.bounded cocone.ι]

instance {F : J ⥤ C} {s : bounded_cocone F} : nat_trans.bounded s.cocone.ι := s.bounded

namespace bounded_cone

structure is_limit {F : J ⥤ C} (t : bounded_cone F) :=
(lift  : Π (s : bounded_cone F), s.cone.X ⟶ t.cone.X)
(fac'  : ∀ (s : bounded_cone F) (j : J), lift s ≫ t.cone.π.app j = s.cone.π.app j . obviously)
(uniq' : ∀ (s : bounded_cone F) (m : s.cone.X ⟶ t.cone.X)
  (w : ∀ j : J, m ≫ t.cone.π.app j = s.cone.π.app j), m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp, reassoc] is_limit.fac
restate_axiom is_limit.uniq'

lemma lift_norm_le {F : J ⥤ C} {t s : bounded_cone F}
  (h : t.is_limit) : s.cone.π.norm ≤ ∥ h.lift s ∥ * t.cone.π.norm :=
begin
  refine real.Inf_le _ ⟨0,λ c hc, hc.1⟩ ⟨mul_nonneg (_root_.norm_nonneg _) (nat_trans.norm_nonneg _),_⟩,
  refine ⟨mul_nonneg (_root_.norm_nonneg _) (nat_trans.norm_nonneg _),λ j, _⟩,
  rw [← h.fac],
  refine le_trans (semi_normed_category.norm_comp _ _ _ _ _) _,
  suffices : ∥ t.cone.π.app j ∥ ≤ t.cone.π.norm,
  { have hh : 0 ≤ ∥ h.lift s ∥ := _root_.norm_nonneg _,
    exact mul_le_mul_of_nonneg_left this hh },
  apply nat_trans.le_norm,
end

end bounded_cone

namespace bounded_cocone

structure is_colimit {F : J ⥤ C} (t : bounded_cocone F) :=
(desc  : Π (s : bounded_cocone F), t.cocone.X ⟶ s.cocone.X)
(fac'  : ∀ (s : bounded_cocone F) (j : J), t.cocone.ι.app j ≫ desc s = s.cocone.ι.app j . obviously)
(uniq' : ∀ (s : bounded_cocone F) (m : t.cocone.X ⟶ s.cocone.X)
  (w : ∀ j : J, t.cocone.ι.app j ≫ m = s.cocone.ι.app j), m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp,reassoc] is_colimit.fac
restate_axiom is_colimit.uniq'

lemma desc_norm_le {F : J ⥤ C} {t s : bounded_cocone F}
  (h : t.is_colimit) : s.cocone.ι.norm ≤ ∥ h.desc s ∥ * t.cocone.ι.norm :=
begin
  refine real.Inf_le _ ⟨0,λ c hc, hc.1⟩ ⟨mul_nonneg (_root_.norm_nonneg _) (nat_trans.norm_nonneg _),_⟩,
  refine ⟨mul_nonneg (_root_.norm_nonneg _) (nat_trans.norm_nonneg _),λ j, _⟩,
  rw [← h.fac],
  refine le_trans (semi_normed_category.norm_comp _ _ _ _ _) _,
  suffices : ∥ t.cocone.ι.app j ∥ ≤ t.cocone.ι.norm,
  { have hh : 0 ≤ ∥ h.desc s ∥ := _root_.norm_nonneg _,
    rw mul_comm,
    exact mul_le_mul_of_nonneg_left this hh },
  apply nat_trans.le_norm,
end

end bounded_cocone

end limits

namespace functor

def map_bounded_cone {F : J ⥤ C} (S : limits.bounded_cone F) :
  limits.bounded_cone (F ⋙ G) :=
{ cone := G.map_cone S.cone,
  bounded := begin
    use S.cone.π.norm,
    refine ⟨S.cone.π.norm_nonneg, S.cone.π.norm_nonneg, _⟩,
    simp [S.cone.π.le_norm],
  end }

def map_bounded_cocone {F : J ⥤ C} (S : limits.bounded_cocone F) :
  limits.bounded_cocone (F ⋙ G) :=
{ cocone := G.map_cocone S.cocone,
  bounded := begin
    use S.cocone.ι.norm,
    refine ⟨S.cocone.ι.norm_nonneg, S.cocone.ι.norm_nonneg, _⟩,
    simp [S.cocone.ι.le_norm],
  end }

end functor

end category_theory
