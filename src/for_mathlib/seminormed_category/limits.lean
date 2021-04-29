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

namespace cone

def bounded_by {F : J ⥤ C} (S : cone F) (c : ℝ) : Prop :=
0 ≤ c ∧ ∀ j : J, ∥ S.π.app j ∥ ≤ c

end cone

namespace cocone

def bounded_by {F : J ⥤ C} (S : cocone F) (c : ℝ) : Prop :=
0 ≤ c ∧ ∀ j : J, ∥ S.ι.app j ∥ ≤ c

end cocone

structure bounded_cone (F : J ⥤ C) :=
(cone : cone F)
(bounded : ∃ c, 0 ≤ c ∧ cone.bounded_by c)

structure bounded_cocone (F : J ⥤ C) :=
(cocone : cocone F)
(bounded : ∃ c, 0 ≤ c ∧ cocone.bounded_by c)

namespace bounded_cone

noncomputable instance {F : J ⥤ C} : has_norm (bounded_cone F) := has_norm.mk $
λ S, Inf { a | 0 ≤ a ∧ S.cone.bounded_by a }

lemma norm_le {F : J ⥤ C} (S : bounded_cone F) (j : J) :
  ∥ S.cone.π.app j ∥ ≤ ∥ S ∥ := real.lb_le_Inf _ S.bounded (λ c hc, hc.2.2 _)

lemma norm_le_of_bounded_by {F : J ⥤ C} (S : bounded_cone F) (a : ℝ)
  (h : S.cone.bounded_by a) : ∥ S ∥ ≤ a :=
begin
  apply real.Inf_le,
  use 0,
  intros c hc, exact hc.1,
  refine ⟨h.1, h⟩,
end

lemma norm_nonneg {F : J ⥤ C} (S : bounded_cone F) : 0 ≤ ∥ S ∥ :=
begin
  apply real.lb_le_Inf,
  exact S.bounded,
  intros c hc, exact hc.1,
end

structure is_limit {F : J ⥤ C} (t : bounded_cone F) :=
(lift  : Π (s : bounded_cone F), s.cone.X ⟶ t.cone.X)
(fac'  : ∀ (s : bounded_cone F) (j : J), lift s ≫ t.cone.π.app j = s.cone.π.app j . obviously)
(uniq' : ∀ (s : bounded_cone F) (m : s.cone.X ⟶ t.cone.X)
  (w : ∀ j : J, m ≫ t.cone.π.app j = s.cone.π.app j), m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp, reassoc] is_limit.fac
restate_axiom is_limit.uniq'

lemma lift_norm_le {F : J ⥤ C} {t s : bounded_cone F}
  (h : t.is_limit) : ∥ s ∥ ≤ ∥ h.lift s ∥ * ∥ t ∥ :=
begin
  refine real.Inf_le _ ⟨0,λ c hc, hc.1⟩ ⟨mul_nonneg (_root_.norm_nonneg _) (norm_nonneg _),_⟩,
  refine ⟨mul_nonneg (_root_.norm_nonneg _) (norm_nonneg _),λ j, _⟩,
  rw [← h.fac],
  refine le_trans (semi_normed_category.norm_comp _ _ _ _ _) _,
  suffices : ∥ t.cone.π.app j ∥ ≤ ∥ t ∥,
  { have hh : 0 ≤ ∥ h.lift s ∥ := _root_.norm_nonneg _,
    exact mul_le_mul_of_nonneg_left this hh },
  apply norm_le,
end

end bounded_cone

namespace bounded_cocone

noncomputable instance {F : J ⥤ C} : has_norm (bounded_cocone F) := has_norm.mk $
λ S, Inf { a | 0 ≤ a ∧ S.cocone.bounded_by a }

lemma norm_le {F : J ⥤ C} (S : bounded_cocone F) (j : J) :
  ∥ S.cocone.ι.app j ∥ ≤ ∥ S ∥ := real.lb_le_Inf _ S.bounded (λ c hc, hc.2.2 _)

lemma norm_le_of_bounded_by {F : J ⥤ C} (S : bounded_cocone F) (a : ℝ)
  (h : S.cocone.bounded_by a) : ∥ S ∥ ≤ a :=
begin
  apply real.Inf_le,
  use 0,
  intros c hc, exact hc.1,
  refine ⟨h.1, h⟩,
end

lemma norm_nonneg {F : J ⥤ C} (S : bounded_cocone F) : 0 ≤ ∥ S ∥ :=
begin
  apply real.lb_le_Inf,
  exact S.bounded,
  intros c hc, exact hc.1,
end

structure is_colimit {F : J ⥤ C} (t : bounded_cocone F) :=
(desc  : Π (s : bounded_cocone F), t.cocone.X ⟶ s.cocone.X)
(fac'  : ∀ (s : bounded_cocone F) (j : J), t.cocone.ι.app j ≫ desc s = s.cocone.ι.app j . obviously)
(uniq' : ∀ (s : bounded_cocone F) (m : t.cocone.X ⟶ s.cocone.X)
  (w : ∀ j : J, t.cocone.ι.app j ≫ m = s.cocone.ι.app j), m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp,reassoc] is_colimit.fac
restate_axiom is_colimit.uniq'

lemma desc_norm_le {F : J ⥤ C} {t s : bounded_cocone F}
  (h : t.is_colimit) : ∥ s ∥ ≤ ∥ h.desc s ∥ * ∥ t ∥ :=
begin
  refine real.Inf_le _ ⟨0,λ c hc, hc.1⟩ ⟨mul_nonneg (_root_.norm_nonneg _) (norm_nonneg _),_⟩,
  refine ⟨mul_nonneg (_root_.norm_nonneg _) (norm_nonneg _),λ j, _⟩,
  rw [← h.fac],
  refine le_trans (semi_normed_category.norm_comp _ _ _ _ _) _,
  suffices : ∥ t.cocone.ι.app j ∥ ≤ ∥ t ∥,
  { have hh : 0 ≤ ∥ h.desc s ∥ := _root_.norm_nonneg _,
    rw mul_comm,
    exact mul_le_mul_of_nonneg_left this hh },
  apply norm_le,
end

end bounded_cocone

end limits

namespace functor

def map_bounded_cone {F : J ⥤ C} (S : limits.bounded_cone F) :
  limits.bounded_cone (F ⋙ G) :=
{ cone := G.map_cone S.cone,
  bounded := begin
    use ∥ S ∥,
    refine ⟨S.norm_nonneg, S.norm_nonneg, _⟩,
    simp [S.norm_le],
  end }

def map_bounded_cocone {F : J ⥤ C} (S : limits.bounded_cocone F) :
  limits.bounded_cocone (F ⋙ G) :=
{ cocone := G.map_cocone S.cocone,
  bounded := begin
    use ∥ S ∥,
    refine ⟨S.norm_nonneg, S.norm_nonneg, _⟩,
    simp [S.norm_le],
  end }

end functor

end category_theory
