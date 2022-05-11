import category_theory.abelian.homology
import category_theory.limits.constructions.epi_mono

namespace category_theory

open category_theory.limits

universes v u

class AB4 (A : Type u) [category.{v} A] [has_coproducts A] : Prop :=
(cond : ∀ {α : Type v} (X Y : α → A) (f : Π a, X a ⟶ Y a)
  (hf : ∀ a, mono (f a)), mono (sigma.desc $ λ a, f a ≫ sigma.ι Y a))

variables {A : Type u} [category.{v} A] [has_coproducts A] [AB4 A]

instance AB4_mono {α : Type v} (X Y : α → A) (f : Π a, X a ⟶ Y a)
  [∀ a, mono (f a)] : mono (sigma.desc $ λ a, f a ≫ sigma.ι Y a) :=
begin
  apply AB4.cond, assumption,
end

variable (A)
noncomputable
def sigma_functor (α : Type v) : (α → A) ⥤ A :=
{ obj := λ X, sigma_obj X,
  map := λ X Y f, sigma.desc $ λ a, f a ≫ sigma.ι _ a } .
variable {A}

instance sigma_functor_preserves_mono (α : Type v)
  {X Y : α → A} (f : X ⟶ Y) [∀ a, mono (f a)] :
  mono ((sigma_functor A α).map f) :=
category_theory.AB4_mono X Y f

instance sigma_functor_preserves_epi (α : Type v)
  {X Y : α → A} (f : X ⟶ Y) [∀ a, epi (f a)] :
  epi ((sigma_functor A α).map f) :=
begin
  constructor, intros Z s t h,
  apply colimit.hom_ext,
  intros a,
  dsimp [sigma_functor] at h,
  apply_fun (λ e, colimit.ι _ a ≫ e) at h,
  simp at h,
  rwa cancel_epi at h,
end

-- TODO: exactness of `sigma_functor`. Mono and Epi conditions done.
-- TODO: homology commutes with coproducts given AB4.
-- TODO: etc...

end category_theory
