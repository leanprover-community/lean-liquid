import topology.discrete_quotient
import topology.category.Profinite
import category_theory.arrow
import data.setoid.partition

import for_mathlib.Profinite.quotient_map

open category_theory

namespace discrete_quotient

universe u
variables {X Y : Profinite.{u}} (f : X ⟶ Y) (surj : function.surjective f)

/-- The relation defining the largest quotient of f.right compatible with S. -/
inductive make_rel (S : discrete_quotient X) : Y → Y → Prop
| of (x y : X) (h : S.rel x y) : make_rel (f x) (f y)
| trans {x y z : Y} : make_rel x y → make_rel y z → make_rel x z

lemma make_rel_impl (S : discrete_quotient X) (x y : X) :
  S.rel x y → S.make_rel f (f x) (f y) := make_rel.of _ _

include surj

lemma make_rel_equiv (S : discrete_quotient X) : equivalence (S.make_rel f) :=
begin
  refine ⟨λ x, _, λ x y h, _, λ x y z h1 h2, make_rel.trans h1 h2⟩,
  { obtain ⟨x,rfl⟩ := surj x,
    exact make_rel.of _ _ (S.refl _) },
  { induction h with x y h1 x y z h1 h2 h3 h4,
    exact make_rel.of y x (S.symm x y h1),
    exact make_rel.trans h4 h3 },
end

/-- The setoid assoc. to make_rel. -/
def make_setoid (S : discrete_quotient X) : _root_.setoid Y :=
⟨S.make_rel f, S.make_rel_equiv f surj⟩

/-- The quotient of make_rel. -/
@[nolint has_inhabited_instance]
def make_quotient (S : discrete_quotient X) : Type* := quotient (S.make_setoid f surj)

/-- The projection onto make_rel. -/
def make_proj (S : discrete_quotient X) : Y → S.make_quotient f surj :=
  quotient.mk'

lemma make_proj_comm (S : discrete_quotient X) :
  S.make_proj f surj ∘ f = (quotient.map' f $ by exact make_rel_impl _ _) ∘ S.proj :=
by {ext, refl}

variable (f)

/-- Given a discrete quotient S of f.left, this is the compatible quotient
 of f where f.right is as large as possible. -/
def make (S : discrete_quotient X) : discrete_quotient Y :=
{ rel := S.make_rel f,
  equiv := S.make_rel_equiv f surj,
  clopen := begin
    intros x,
    have : set_of (S.make_rel f x) = S.make_proj f surj ⁻¹' {S.make_proj f surj x},
    { dsimp [make_proj],
      ext,
      simp only [set.mem_preimage, set.mem_singleton_iff, quotient.eq', set.mem_set_of_eq],
      refine ⟨λ h, setoid.symm' _ h, λ h, setoid.symm' _ h⟩ },
    rw this,
    letI : topological_space (S.make_quotient f surj) := ⊥,
    haveI : discrete_topology (S.make_quotient f surj) := ⟨rfl⟩,
    suffices : continuous (S.make_proj f surj),
    { refine ⟨is_open.preimage this trivial, is_closed.preimage this ⟨trivial⟩⟩ },
    rw [(Profinite.quotient_map f surj).continuous_iff, S.make_proj_comm f surj],
    exact continuous_bot.comp (proj_continuous S),
  end }

lemma make_le_comap (S : discrete_quotient X) : le_comap f.continuous S (S.make f surj) :=
make_rel_impl _ _

lemma make_right_le (S : discrete_quotient X) (T : discrete_quotient Y)
  (compat : le_comap f.continuous S T) :
  (S.make f surj) ≤ T :=
begin
  intros x y h,
  induction h with a b hab a b c _ _ h1 h2,
  { exact compat a b hab },
  { exact trans T a b c h1 h2 },
end

lemma make_right_mono (S1 S2 : discrete_quotient X) (h : S1 ≤ S2) :
  S1.make f surj ≤ S2.make f surj :=
begin
  intros x y h,
  induction h,
  { refine make_rel.of _ _ (h _ _ _),
  assumption },
  { apply make_rel.trans,
    assumption' },
end

end discrete_quotient
