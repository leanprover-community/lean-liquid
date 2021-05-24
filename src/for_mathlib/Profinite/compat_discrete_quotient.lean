import topology.discrete_quotient
import topology.category.Profinite
import category_theory.arrow
import data.setoid.partition

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

-- A surjective map of compact Hausdorff spaces is a quotient map
-- TODO: This certainly belongs in mathlib, if not already there...
lemma quotient_map : quotient_map f :=
begin
  rw quotient_map_iff,
  refine ⟨surj,_⟩,
  intro S,
  split,
  { intro hS,
    exact is_open.preimage f.continuous hS },
  { intro hS,
    rw ← is_closed_compl_iff at *,
    rw ← set.preimage_compl at hS,
    have : Sᶜ = f '' (f ⁻¹' Sᶜ),
    { ext,
      split,
      { intro h,
        obtain ⟨y,rfl⟩ := surj x,
        refine ⟨y,h,rfl⟩ },
      { rintro ⟨y,h,rfl⟩,
        exact h } },
    rw this,
    apply Profinite.is_closed_map f,
    assumption }
end

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
    { split,
      apply is_open.preimage this trivial,
      apply is_closed.preimage this ⟨trivial⟩ },
    rw (quotient_map f surj).continuous_iff,
    rw S.make_proj_comm f surj,
    apply continuous.comp,
    continuity,
    exact S.proj_continuous,
  end }

lemma make_le_comap (S : discrete_quotient X) : le_comap f.continuous S (S.make f surj) :=
make_rel_impl _ _

/-
/-- make as an arrow. -/
def make_arrow (S : discrete_quotient X) : arrow Profinite :=
{ left := Profinite.of S,
  right := Profinite.of (S.make surj),
  hom := ⟨discrete_quotient.map (S.make_le_comap surj)⟩ }

/-- the canonical morphism of arrows to make. -/
def make_hom (S : discrete_quotient X) : f ⟶ S.make_arrow surj :=
{ left := ⟨S.proj, S.proj_continuous⟩,
  right := ⟨(S.make surj).proj, (S.make surj).proj_continuous⟩ }
-/

lemma make_right_le (S : discrete_quotient X) (T : discrete_quotient Y)
  (compat : le_comap f.continuous S T) :
  (S.make f surj) ≤ T :=
begin
  intros x y h,
  induction h with a b hab a b c _ _ h1 h2,
  apply compat,
  assumption,
  apply T.trans _ _ _ h1 h2,
end

lemma make_right_mono (S1 S2 : discrete_quotient X) (h : S1 ≤ S2) :
  S1.make f surj ≤ S2.make f surj :=
begin
  intros x y h,
  induction h,
  apply make_rel.of,
  apply h,
  assumption,
  apply make_rel.trans,
  assumption',
end

end discrete_quotient
