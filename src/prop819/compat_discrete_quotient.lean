import topology.discrete_quotient
import topology.category.Profinite
import category_theory.arrow
import data.setoid.partition

open category_theory

/-- A compatible system of discrete quotients. -/
@[nolint has_inhabited_instance]
structure compat_discrete_quotient (f : arrow Profinite) :=
(left : discrete_quotient f.left)
(right : discrete_quotient f.right)
(compat' [] : discrete_quotient.le_comap f.hom.continuous left right . obviously)

restate_axiom compat_discrete_quotient.compat'

namespace discrete_quotient

variables {f : arrow Profinite} (surj : function.surjective f.hom)

/-- The relation defining the largest quotient of f.right compatible with S. -/
inductive make_rel (S : discrete_quotient f.left) : f.right → f.right → Prop
| of (x y : f.left) (h : S.rel x y) : make_rel (f.hom x) (f.hom y)
| trans {x y z : f.right} : make_rel x y → make_rel y z → make_rel x z

lemma make_rel_impl (S : discrete_quotient f.left) (x y : f.left) :
  S.rel x y → S.make_rel (f.hom x) (f.hom y) := make_rel.of _ _

include surj

lemma make_rel_equiv (S : discrete_quotient f.left) : equivalence S.make_rel :=
begin
  refine ⟨_,_,_⟩,
  { intro x,
    obtain ⟨x,rfl⟩ := surj x,
    apply make_rel.of,
    apply S.refl },
  { intros x y h,
    induction h with x y h1 x y z h1 h2 h3 h4,
    apply make_rel.of,
    apply S.symm _ _ h1,
    apply make_rel.trans,
    assumption' },
  { intros x y z h1 h2,
    apply make_rel.trans,
    assumption' }
end

/-- The setoid assoc. to make_rel. -/
def make_setoid (S : discrete_quotient f.left) : _root_.setoid f.right :=
⟨S.make_rel, S.make_rel_equiv surj⟩

/-- The quotient of make_rel. -/
@[nolint has_inhabited_instance]
def make_quotient (S : discrete_quotient f.left) : Type* := quotient (S.make_setoid surj)

/-- The projection onto make_rel. -/
def make_proj (S : discrete_quotient f.left) : f.right → S.make_quotient surj :=
  quotient.mk'

lemma make_proj_comm (S : discrete_quotient f.left) :
  S.make_proj surj ∘ f.hom = (quotient.map' f.hom $ by exact make_rel_impl _) ∘ S.proj :=
by {ext, refl}

variable (f)

-- A surjective map of compact Hausdorff spaces is a quotient map
-- TODO: This certainly belongs in mathlib, if not already there...
lemma quotient_map : quotient_map f.hom :=
begin
  rw quotient_map_iff,
  refine ⟨surj,_⟩,
  intro S,
  split,
  { intro hS,
    exact is_open.preimage f.hom.continuous hS },
  { intro hS,
    rw ← is_closed_compl_iff at *,
    rw ← set.preimage_compl at hS,
    have : Sᶜ = f.hom '' (f.hom ⁻¹' Sᶜ),
    { ext,
      split,
      { intro h,
        obtain ⟨y,rfl⟩ := surj x,
        refine ⟨y,h,rfl⟩ },
      { rintro ⟨y,h,rfl⟩,
        exact h } },
    rw this,
    apply Profinite.is_closed_map f.hom,
    assumption }
end

variable {f}

/-- Given a discrete quotient S of f.left, this is the compatible quotient
 of f where f.right is as large as possible. -/
def make (S : discrete_quotient f.left) : compat_discrete_quotient f :=
{ left := S,
  right :=
  { rel := make_rel S,
    equiv := S.make_rel_equiv surj,
    clopen := begin
      intros x,
      have : set_of (S.make_rel x) = S.make_proj surj ⁻¹' {S.make_proj surj x},
      { dsimp [make_proj],
        ext,
        simp only [set.mem_preimage, set.mem_singleton_iff, quotient.eq', set.mem_set_of_eq],
        refine ⟨λ h, setoid.symm' _ h, λ h, setoid.symm' _ h⟩ },
      rw this,
      letI : topological_space (S.make_quotient surj) := ⊥,
      haveI : discrete_topology (S.make_quotient surj) := ⟨rfl⟩,
      suffices : continuous (S.make_proj surj),
      { split,
        apply is_open.preimage this trivial,
        apply is_closed.preimage this ⟨trivial⟩ },
      rw (quotient_map f surj).continuous_iff,
      rw S.make_proj_comm surj,
      apply continuous.comp,
      continuity,
      exact S.proj_continuous,
    end },
  compat' := make_rel_impl _ }

end discrete_quotient
