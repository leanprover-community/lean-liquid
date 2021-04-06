import topology.category.Profinite

open category_theory

namespace Profinite

-- Here we prove that the category of profinite sets has limits.

universe u

-- TODO: Show that Profinite_to_Top creates limit.
-- Note that the limits in Top are defined using infemum of various topologies
-- and this makes proving the t2_space, totally_disconnected_space and compact_space
-- instances somewhat more annoying.
-- By using a subtype, the typeclass system finds t2_space and totally_disconnected_space
-- automatically.
-- Proving compactness boils down to noting that the equations defining this subtype give a
-- closed condition.

def limit_cone {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) : limits.cone F :=
{ X := let S := {u : Π (j : J), (F.obj j) | ∀ {j j' : J} (f : j ⟶ j'), (F.map f) (u j) = u j'} in
  { to_Top := { α := S },
    is_compact := begin
      erw ← compact_iff_compact_space,
      apply is_closed.compact,
      have : S = ⋂ (a b : J) (f : a ⟶ b), { u : Π (j : J), F.obj j | F.map f (u a) = u b },
        by tidy,
      rw this, clear this,
      apply is_closed_Inter,
      intros a,
      apply is_closed_Inter,
      intros b,
      apply is_closed_Inter,
      intros f,
      let π : (Π (j : J), F.obj j) → F.obj a × F.obj b := λ x, (x a, x b),
      change is_closed (π ⁻¹' { x | F.map f x.1 = x.2 }),
      refine is_closed.preimage (continuous.prod_mk (continuous_apply _) (continuous_apply _)) _,
      refine is_closed_eq _ continuous_snd,
      continuity,
    end },
  π :=
  { app := λ j,
    { to_fun := (λ t : (Π (j : J), F.obj j), t j) ∘ subtype.val,
      continuous_to_fun := continuous.comp (continuous_apply _) continuous_subtype_val } } }

def is_limit_limit_cone {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) :
  limits.is_limit (limit_cone F) :=
{ lift := λ S,
  { to_fun := λ x,
    { val := λ j, S.π.app j x,
      property := begin
        intros a b f,
        dsimp,
        rw ← S.w f,
        refl,
      end } },
  uniq' := begin
    intros S m h,
    ext x j,
    dsimp,
    rw ← h,
    refl,
  end }.

instance : limits.has_limits Profinite := limits.has_limits.mk $
λ J hJ, { has_limit := λ F, { exists_limit := nonempty.intro $ by exactI
  { cone := limit_cone F,
    is_limit := is_limit_limit_cone _ } } }

end Profinite
