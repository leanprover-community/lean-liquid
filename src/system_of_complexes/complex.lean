import category_theory.graded_object
import category_theory.preadditive
import category_theory.abelian.additive_functor
import data.int.basic

-- remove this
import tactic
/-!

# Contents

1) technical `succ` stuff -- `has_succ` class

2) eq_to_hom -- technical rewrite hack

-/
open category_theory category_theory.limits

section succ_pred

variables (α : Type*)

class has_succ := (succ : α → α)

class has_succ_pred extends α ≃ α.

instance has_succ_pred.has_succ [e : has_succ_pred α] : has_succ α :=
⟨e.to_equiv⟩

variables {α}

-- fix this to something better?
def succ [has_succ α] (a : α) := has_succ.succ a
def succ_equiv (α) [has_succ_pred α] : equiv.perm α := has_succ_pred.to_equiv
def pred [has_succ_pred α] (a : α) := (succ_equiv α).symm a

variables [has_succ_pred α] (a : α)

@[simp] lemma coe_succ_equiv : (succ_equiv α : α → α) = succ := rfl

lemma succ_equiv_apply : succ_equiv α a = succ a := rfl

@[simp] lemma succ_pred : succ (pred a) = a :=
equiv.apply_symm_apply _ a

@[simp] lemma pred_succ : pred (succ a) = a :=
equiv.symm_apply_apply _ a

-- do we want this for every semiring??
instance : has_succ ℕ := ⟨λ n, n + 1⟩
instance : has_succ_pred ℤ :=
{ to_fun := λ n, n + 1,
  inv_fun := λ n, n - 1,
  left_inv := λ n, add_sub_cancel n 1,
  right_inv := λ n, sub_add_cancel n 1 }

@[simp] lemma succ_nat (n : ℕ) : succ n = n + 1 := rfl
@[simp] lemma succ_int (n : ℤ) : succ n = n + 1 := rfl
@[simp] lemma pred_int (n : ℤ) : pred n = n - 1 := rfl

end succ_pred

/-

## Differential Objects

A differential object is a "lawless complex".

When we write

```
structure group (G : Type) [has_mul G] [has_one G] [has_inv G]
(mul_one : ∀ g, g * 1 = g)
(whatever the other actual axioms are in the chosen definition)
```

we see that mathematicians are very quick to
want to fix and use our *interface* (in particular
infix `*` notation -- infix is some form
of Curry-Howard? ) for their definitions,
but don't care about
which of the standard group-theoretic
facts are axioms and which were proved
as theorems (the difference between
propositional and definitional equality),
we just want the `group.foo` interface

A differential object seems to be the same
kind of thing but one level up. If `V` is
a category (for example the category of abelian groups)
and `ι` is a type (for example the integers), then
an `ι`-graded differential `V`-object has at its
heart a "function from `ι` to `V`" (there are set-theoretic issues here).
Mathematicians often write "a collection of objects `Xₙ` for `n in ι`",
in a passing nod to the issues. We also want to talk
about maps between these objects, and sometimes they go
from `X_i` to `X_{i+1}` but sometimes some of them go from `X_{i,j}`
to `X_{i,j-1}` or there are several things all called variants
of `d` forming a grid of commuting squares or anticommuting
squares. The thing which we are proposing in to model this
situation is a `differential_object`, which comes equipped
a map called `d` once and for all, which is maps $$X_i\to X_j$$
for all $$i$$ and $$j$$ in `ι`.

The trick we will use later when working with complexes is
that all of the `d`s other than the ones we're interested in
are simply defined to be `0`. We have this option because
we are working in a preadditive category.

-/
@[ext]
structure differential_object (ι : Type) (V : Type*) [category V] :=
(X : ι → V)
(d : Π i j, X i ⟶ X j)

variables (ι : Type) (V : Type*) {cov : bool}

namespace differential_object
variables [category V]

variables{ι V} (C C₁ C₂ C₃ : differential_object ι V)

section category
/-!
A morphism between differential objects $$X=((X_n)_{n\in i},d)$$ and $Y$
is a collection of morphisms `f n : X n ⟶ Y n` which commute with `d`
in the obvious way.
-/
@[ext]
structure hom :=
(f (i : ι) : C₁.X i ⟶ C₂.X i)
(comm (i j : ι) : C₁.d i j ≫ f j = f i ≫ C₂.d i j)

attribute [reassoc] hom.comm

variables {C₁ C₂ C₃}

/-! The identity differential object -/
protected def id : hom C C :=
{ f := λ i, 𝟙 _,
  comm := by { intros, rw [category.id_comp, category.comp_id] } }

/-! Composition of differential objects the "right-action" way -/
def comp (f : hom C₁ C₂) (g : hom C₂ C₃) : hom C₁ C₃ :=
{ f := λ i, f.f i ≫ g.f i,
  comm := λ i j, by { rw [hom.comm_assoc, hom.comm, category.assoc] } }

/-! Differential objects are a category. -/
instance : category (differential_object ι V) :=
{ hom := hom,
  id := differential_object.id,
  comp := λ _ _ _, comp,
  id_comp' := by { intros, ext, exact category.id_comp _ },
  comp_id' := by { intros, ext, exact category.comp_id _ },
  assoc' := by { intros, ext, dsimp [id, comp], rw [category.assoc] } }

@[simp] lemma id_f (i : ι) : (𝟙 C : C ⟶ C).f i = 𝟙 (C.X i) := rfl

@[simp] lemma comp_f (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  (f ≫ g).f i = f.f i ≫ g.f i := rfl

/-!
X₁ i --h=-> X₁ j
 |            |
 | fᵢ         | fⱼ
 \/           \/
 X₂ i --h=-> X₂ j
-/
@[simp, reassoc]
lemma eq_to_hom_f (f : C₁ ⟶ C₂) (i j : ι) (h : i = j) :
  eq_to_hom (congr_arg _ h) ≫ f.f j = f.f i ≫ eq_to_hom (congr_arg _ h) :=
by { cases h, simp only [eq_to_hom_refl, category.id_comp, category.comp_id] }

/-!
Ask on Zulip : Should we have a "simp lemma order" for commutative squares?

       X i -hi⟶ X i'
       |          |
       | d        | d
      \/         \/
      X j -hj-> X j'
-/
@[simp, reassoc]
lemma eq_to_hom_d (i i' j j' : ι) :
  ∀ (hi : i = i') (hj : j = j'),
  eq_to_hom (congr_arg _ hi) ≫ C.d i' j' = C.d i j ≫ eq_to_hom (congr_arg _ hj) :=
by { rintro rfl rfl, simp only [eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simps]
def iso_app (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
{ hom := f.hom.f i,
  inv := f.inv.f i,
  hom_inv_id' := by { rw [← comp_f, f.hom_inv_id, id_f] },
  inv_hom_id' := by { rw [← comp_f, f.inv_hom_id, id_f] } }

@[simps]
def iso_of_components (f : Π i, C₁.X i ≅ C₂.X i)
  (hf : ∀ i j, C₁.d i j ≫ (f j).hom = (f i).hom ≫ C₂.d i j) :
  C₁ ≅ C₂ :=
{ hom :=
  { f := λ i, (f i).hom,
    comm := hf },
  inv :=
  { f := λ i, (f i).inv,
    comm := λ i j,
    calc C₂.d i j ≫ (f j).inv
        = (f i).inv ≫ ((f i).hom ≫ C₂.d i j) ≫ (f j).inv : by simp
    ... = (f i).inv ≫ (C₁.d i j ≫ (f j).hom) ≫ (f j).inv : by rw hf
    ... = (f i).inv ≫ C₁.d i j : by simp },
  hom_inv_id' := by { ext i, exact (f i).hom_inv_id },
  inv_hom_id' := by { ext i, exact (f i).inv_hom_id } }

instance [has_zero_morphisms V] : has_zero_morphisms (differential_object ι V) :=
{ has_zero := λ C₁ C₂, ⟨{ f := λ i, 0, comm := λ _ _, by rw [zero_comp, comp_zero] }⟩,
  comp_zero' := by { intros, ext, rw [comp_f, comp_zero] },
  zero_comp' := by { intros, ext, rw [comp_f, zero_comp] } }

section preadditive

open category_theory.preadditive

variables [preadditive V]

instance : has_add (C₁ ⟶ C₂) :=
⟨λ f g, { f := λ i, f.f i + g.f i, comm := λ i j, by rw [comp_add, add_comp, f.comm, g.comm] }⟩

instance : has_sub (C₁ ⟶ C₂) :=
⟨λ f g, { f := λ i, f.f i - g.f i, comm := λ i j, by rw [comp_sub, sub_comp, f.comm, g.comm] }⟩

instance : has_neg (C₁ ⟶ C₂) :=
⟨λ f, { f := λ i, -f.f i, comm := λ i j, by rw [comp_neg, neg_comp, f.comm] }⟩

@[simp] lemma add_f (f g : C₁ ⟶ C₂) (i : ι) : (f + g).f i = f.f i + g.f i := rfl

@[simp] lemma sub_f (f g : C₁ ⟶ C₂) (i : ι) : (f - g).f i = f.f i - g.f i := rfl

@[simp] lemma neg_f (f : C₁ ⟶ C₂) (i : ι) : (-f).f i = -f.f i := rfl

instance : add_comm_group (C₁ ⟶ C₂) :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  sub := has_sub.sub,
  add_assoc := by { intros, ext, apply add_assoc },
  zero_add := by { intros, ext, apply zero_add },
  add_zero := by { intros, ext, apply add_zero },
  sub_eq_add_neg := by {intros, ext, apply sub_eq_add_neg },
  add_left_neg := by {intros, ext, apply add_left_neg },
  add_comm := by {intros, ext, apply add_comm } }

variables (ι V)

/-! If `V` is pre-additive, the differential object category is pre-additive. -/
instance : preadditive (differential_object ι V) :=
{ hom_group := λ C₁ C₂, infer_instance,
  add_comp' := by { intros, ext, simp only [comp_f, add_f, add_comp] },
  comp_add' := by { intros, ext, simp only [comp_f, add_f, comp_add] } }

/-

## succ and differential objects

This is the pushforward
-/
def comap (V : Type*) [category V] [preadditive V] {ι1 ι2 : Type}
  (g : ι1 → ι2) : differential_object ι2 V ⥤ differential_object ι1 V :=
{ obj := λ C,
  { X := λ i, C.X (g i),
    d := λ i j, C.d _ _ }, -- no sign shift
  map := λ C₁ C₂ f,
  { f := λ i, f.f (g i),
    comm := λ i j, by simp only [f.comm]} }

def neg_d (V : Type*) [category V] [preadditive V] {ι : Type}
  : differential_object ι V ⥤ differential_object ι V :=
{ obj := λ C,
  { X := λ i, C.X i,
    d := λ i j, -C.d _ _ },
  map := λ C₁ C₂ f,
  { f := λ i, f.f i,
    comm := λ i j, by simp [neg_comp, f.comm] } }

@[simps]
def shift [has_succ ι] :
  differential_object ι V ⥤ differential_object ι V :=
{ obj := λ C,
  { X := λ i, C.X (succ i),
    d := λ i j, -C.d _ _ },
  map := λ C₁ C₂ f,
  { f := λ i, f.f (succ i),
    comm := λ i j, by simp only [neg_comp, comp_neg, neg_inj, f.comm] } }

-- example [has_succ ι] : shift ι V = neg_d V ⋙ comap V has_succ.succ :=
-- by tidy -- fast

--example [has_succ ι] : shift ι V = comap V has_succ.succ ⋙ neg_d V :=
-- by tidy -- fast

@[simps]
def iso_shift' [has_succ ι] (C : differential_object ι V) (i : ι) :
  ((shift ι V).obj C).X i ≅ C.X (succ i) := iso.refl _

variables [has_succ_pred ι]

instance fo : has_shift (differential_object ι V) :=
{ shift :=
  { functor := shift ι V,
    inverse := @shift ι V _ _ ⟨pred⟩,
    unit_iso := nat_iso.of_components
      (λ C, iso_of_components (λ i, eq_to_iso $ congr_arg C.X $ (succ_pred i).symm)
        (λ i j, by { dsimp, rw [neg_neg, eq_to_hom_d] }))
      (λ C₁ C₂ f, by { ext i, dsimp, rw [eq_to_hom_f] }),
    counit_iso := nat_iso.of_components
      (λ C, iso_of_components (λ i, eq_to_iso $ congr_arg C.X $ pred_succ i)
        (λ i j, by { dsimp, rw [neg_neg, ← eq_to_hom_d] }))
      (λ C₁ C₂ f, by { ext i, dsimp, rw [← eq_to_hom_f] }),
    functor_unit_iso_comp' :=
    by { intros, ext i, dsimp, simp only [eq_to_hom_refl, eq_to_hom_trans] } } }
.
variables {ι V}

@[simps] def iso_shift_zero : C⟦0⟧ ≅ C := iso.refl _

@[simps] def iso_shift_one (i : ι) : C⟦1⟧.X i ≅ C.X (succ i) := iso.refl _

@[simps] def iso_shift_neg_one (i : ι) : C⟦-1⟧.X i ≅ C.X (pred i) := iso.refl _

-- #print equivalence.int.has_pow

-- def iso_shift : ∀ (i : ι) (n : ℤ), C⟦n⟧.X i ≅ C.X (((succ_equiv ι)^n : equiv.perm ι) i)
-- | i (0:ℕ)       := iso_app (iso_shift_zero _) i
-- | i (1:ℕ)       := iso_shift_one _ _
-- | i (n+2:ℕ)     :=
--  by { simp,
--   change (((category_theory.shift (differential_object ι V)).trans
--    (category_theory.shift (differential_object ι V))^((n+1:ℕ) : ℤ)).functor.obj C).X i ≅ _,
--   let f := iso_shift (succ i) (n+1),  }
-- | i -[1+ 0]     := iso_shift_neg_one _ _
-- | i -[1+ (n+1)] := _

end preadditive

variables (ι V)

@[simps]
def forget : differential_object ι V ⥤ graded_object ι V :=
{ obj := λ C, C.X,
  map := λ _ _ f, f.f }

end category

/-
failed to synthesize type class instance for
V : Type uV,
_inst_1 : category V,
_inst_2 : has_zero_morphisms V,
_inst_3 : has_equalizers V,
_inst_4 : has_images V,
A B B' C : V,
f : A ⟶ B,
g : B ⟶ C,
g' : B' ⟶ C,
ι : Type,
P Q R : differential_object ι V,
φ : P ⟶ Q,
ψ : Q ⟶ R
⊢ has_images (differential_object ι V)
-/
--#check is_image -- this is data :-/
--#check has_image -- Prop which says "there exists an image_factorisation"
--#check image_factorisation
-- Data exhibiting that a morphism `f` has an image. -/
-- it's a type whose terms hold two pieces of data,
-- `F : mono_factorisation f` and `is_image : is_image F`
/-
-- need image_factorisation φ for the below
structure image_factorisation (f : X ⟶ Y) :=
(F : mono_factorisation f)
(is_image : is_image F)
-/
--#check classical.choice
--#where
--#check mono_factorisation -- structure, needs I, m and e
--#print mono_factorisation
variable (D : differential_object ι V)
def thing (φ : C ⟶ D) (h : ∀ (i : ι), mono_factorisation (φ.f i)) :
  mono_factorisation φ :=
{ I -- ⊢ differential_object ι V
    := { X := λ a, (h a).I,
         d := λ a b,
         begin
           cases (h a) with aI am ahm_mono ae afac,
           dsimp,
           dsimp at afac,
           cases (h b) with bI bm bhm_mono be bfac,
           dsimp,
           dsimp at bfac,
           have phi_tofun_a := φ.f a,
           have phi_tofun_b := φ.f b,
           have phithing1 := φ.comm a b,
           have phithing2 := φ.comm a a,
           have phithing3 := φ.comm b a,
           have phithing4 := φ.comm b b,
           cases ahm_mono,
           cases bhm_mono,
           -- hey Bhavik what do you think
           -- of this?
           clear h, -- TODO -- DID I BREAK IT

           sorry
         end
         },
  m := sorry,
  m_mono := sorry,
  e := sorry,
  fac' := sorry }

instance foo [has_images V] : has_images (differential_object ι V) :=
{ has_image := λ X Y φ, begin
    unfreezingI {
      obtain ⟨(h : ∀ {A B : V} (f : A ⟶ B), category_theory.limits.has_image f)⟩ := _inst_2 },
    -- grr
    -- this second unfreezing is just for notational reasons
    -- and might be a bug
    unfreezingI {
    change ∀ {A B : V} (f : A ⟶ B), category_theory.limits.has_image f at h },
    -- hooray
    -- ⊢ has_image φ
    constructor,
    existsi _,
    -- ⊢ image_factorisation φ
    exact {
      F -- : mono_factorisation φ
        :=
      { I := (
        { X := λ i, (classical.choice (h (φ.f i)).1).F.1,
          d := begin
            intros i j,
            have h2 := h (X.d i j),
--        apply differential_object.d,
        -- previous line doesn't work
        sorry
      end } : differential_object ι V),
        m -- : I ⟶ Y
          :=
          (sorry : _ ⟶ Y),
        e := (sorry : X ⟶ _),
        -- } next line should be infer_instance
        m_mono := sorry },
      is_image := sorry
    },
  end }

/-
⊢ has_equalizers (differential_object ι V)
-/
instance bar [has_equalizers V] : has_equalizers (differential_object ι V) := sorry

end differential_object
namespace differential_object

variables {ι V} [has_succ ι] [category V] [has_zero_morphisms V]

/-

We need to start turning our lawless complexes into sensible
things like complexes
-/
/-- -/
def coherent_indices : Π (cov : bool) (i j : ι), Prop
| ff i j := i = succ j
| tt i j := succ i = j

variables (ι V)

set_option old_structure_cmd true
/-
Imagine a usual complex of abelian groups, indexed by the naturals or
integers. Now add 0 maps between each pair of abelian groups which
didn't have a map between them before. I claim that d^2=0, where d
is that crazy map defined above.
Indeed, the only way d itself can't be zero is if it's one of the
maps in the original complex, and the composition of any two such
maps is zero whenever it is defined.

If furthermore ι has a `succ` then there are two conventions,
one with `d : X_i → X_{succ i}` and one with `d : X_{succ i} → X_i`.

The below definition makes me wonder whether `d_comp_d = 0`
should be added as a `single_complex_like` axiom.
-/
@[ext]
structure complex_like (cov : bool) extends differential_object ι V :=
(d_comp_d : ∀ i j k, d i j ≫ d j k = 0)
(d_eq_zero : ∀ ⦃i j⦄, ¬ coherent_indices cov i j → d i j = 0)

/-

## main definitions for `complex_like`

The key one is that if `V` is preadditive then so is `complex_like ι V`
if `ι` just means "a type, a succ-structure, and a sign convention"
  I will just call them complexes of V's, with ι = ℤ or ℕ and the
  usual succ and an arbitrary convention for whether d's go up or down.

-/
variables {ι V}

instance coherent_indices_decidable [decidable_eq ι] (cov : bool) (i j : ι) :
  decidable (coherent_indices cov i j) :=
by { cases cov; dsimp [coherent_indices]; apply_instance }

instance : category (complex_like ι V cov) :=
induced_category.category complex_like.to_differential_object

-- generalise this to arbitrary induced categories
instance [has_zero_morphisms V] : has_zero_morphisms (complex_like ι V cov) :=
{ has_zero := λ C₁ C₂,
  show has_zero (C₁.to_differential_object ⟶ C₂.to_differential_object), by apply_instance,
  comp_zero' := λ _ _ _ _, comp_zero,
  zero_comp' := λ _ _ _ _, zero_comp }

-- generalise this to arbitrary induced categories
instance [preadditive V] : preadditive (complex_like ι V cov) :=
{ hom_group := λ C₁ C₂,
  show add_comm_group (C₁.to_differential_object ⟶ C₂.to_differential_object), by apply_instance,
  add_comp' := by { intros, apply preadditive.add_comp },
  comp_add' := by { intros, apply preadditive.comp_add } }

variables {C₁ C₂ : complex_like ι V cov}
/-! Constructor for morphisms of complexes which chases all the diagrams
  with zero in it so you don't have to -/
@[simps]
def hom.mk' (f : Π i, C₁.X i ⟶ C₂.X i)
  (hf : ∀ i j, coherent_indices cov i j → C₁.d i j ≫ f j = f i ≫ C₂.d i j) :
  C₁ ⟶ C₂ :=
{ f := f,
  comm := λ i j,
  begin
    by_cases h : coherent_indices cov i j,
    { exact hf i j h },
    { show C₁.d i j ≫ f j = f i ≫ C₂.d i j,
      rw [C₁.d_eq_zero h, C₂.d_eq_zero h, zero_comp, comp_zero] }
  end }

@[simps]
def complex_like.iso_app (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
{ hom := f.hom.f i,
  inv := f.inv.f i,
  hom_inv_id' := by { erw [← comp_f, f.hom_inv_id, id_f], refl },
  inv_hom_id' := by { erw [← comp_f, f.inv_hom_id, id_f], refl } }

structure is_complex_like (C : differential_object ι V) (cov : bool) : Prop :=
(d_comp_d : ∀ i j k, C.d i j ≫ C.d j k = 0)
(d_eq_zero : ∀ ⦃i j⦄, ¬ coherent_indices cov i j → C.d i j = 0)

abbreviation is_cochain_complex (C : differential_object ι V) := C.is_complex_like tt
abbreviation is_chain_complex (C : differential_object ι V) := C.is_complex_like ff

lemma complex_like.is_complex_like (X : complex_like ι V cov) :
  X.to_differential_object.is_complex_like cov :=
{ .. X }

lemma is_complex_like.iso {C₁ C₂ : differential_object ι V}
  (h : C₁.is_complex_like cov) (f : C₁ ≅ C₂) :
  C₂.is_complex_like cov :=
{ d_comp_d := λ i j k,
  begin
    calc C₂.d i j ≫ C₂.d j k
        = C₂.d i j ≫ C₂.d j k ≫ f.inv.f k ≫ f.hom.f k : _
    ... = f.inv.f i ≫ C₁.d i j ≫ C₁.d j k ≫ f.hom.f k : _
    ... = 0 : _,
    { rw [← comp_f, f.inv_hom_id, id_f, category.comp_id] },
    { simp only [f.inv.comm_assoc] },
    { slice_lhs 2 3 { rw h.d_comp_d }, rw [zero_comp, comp_zero] }
  end,
  d_eq_zero := λ i j hij,
  begin
    calc C₂.d i j = C₂.d i j ≫ f.inv.f j ≫ f.hom.f j : _
    ... = 0 : _,
    { rw [← comp_f, f.inv_hom_id, id_f, category.comp_id] },
    { rw [f.inv.comm_assoc, h.d_eq_zero hij, zero_comp, comp_zero] }
  end }

@[simps]
def mk_complex_like (C : differential_object ι V) (hC : C.is_complex_like cov) :
  complex_like ι V cov :=
{ .. C, .. hC }

@[simps]
def mk_complex_like_iso (C : differential_object ι V) (hC : C.is_complex_like cov) :
  (induced_functor complex_like.to_differential_object).obj (C.mk_complex_like hC) ≅ C :=
eq_to_iso $ by { cases C, refl }

section lift_functor

variables {C : Type*} [category C] (F : C ⥤ differential_object ι V)

@[simps]
def lift_functor (h : ∀ X, (F.obj X).is_complex_like cov) :
  C ⥤ complex_like ι V cov :=
{ obj := λ X, (F.obj X).mk_complex_like (h X),
  map := λ X Y f, show ((F.obj X).mk_complex_like (h X)).to_differential_object ⟶ _,
    from ((F.obj X).mk_complex_like_iso (h X)).hom ≫ F.map f ≫
         ((F.obj Y).mk_complex_like_iso (h Y)).inv,
  map_id' := λ X,
  by { dsimp, simp only [category.id_comp, category_theory.functor.map_id,
    eq_to_hom_refl, eq_to_hom_trans], refl },
  map_comp' := λ X Y Z f g,
  begin
    dsimp,
    erw [category.assoc, category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl,
      category.id_comp, category_theory.functor.map_comp, category.assoc]
  end }

@[simps]
def lift_functor_nat_iso (h : ∀ X, (F.obj X).is_complex_like cov) :
  (lift_functor F h) ⋙ (induced_functor complex_like.to_differential_object) ≅ F :=
nat_iso.of_components (λ X, mk_complex_like_iso _ _) $ λ X Y f,
by { rw [← iso.eq_comp_inv, category.assoc], refl }

lemma lift_functor_d (h : ∀ X, (F.obj X).is_complex_like cov) (x : C) (i j : ι) :
  ((lift_functor F h).obj x).d i j = (F.obj x).d i j :=
rfl

end lift_functor

-- this is a major pain, but we might not need it
-- def lift_equivalence (F : differential_object ι V ≌ differential_object ι V)
--   (h : ∀ X, (F.functor.obj X).is_complex_like cov ↔ X.is_complex_like cov) :
--   complex_like ι V cov ≌ complex_like ι V cov :=
-- { functor := lift_functor ((induced_functor complex_like.to_differential_object) ⋙ F.functor) $
--     by { intro X, dsimp, rw h, exact X.is_complex_like },
--   inverse := lift_functor ((induced_functor complex_like.to_differential_object) ⋙ F.inverse) $
--     by { intro X, dsimp, rw ← h, apply X.is_complex_like.iso, exact (F.counit_iso.app _).symm },
--   unit_iso := nat_iso.of_components admit admit,
--   counit_iso := admit,
--   functor_unit_iso_comp' := admit }

end differential_object

namespace differential_object

namespace complex_like

variables [has_succ_pred ι] [category V] [preadditive V]

open category_theory.preadditive

@[simps]
def shift : complex_like ι V cov ⥤ complex_like ι V cov :=
lift_functor ((induced_functor complex_like.to_differential_object) ⋙ shift ι V)
begin
  rintro ⟨X, d, h1, h2⟩,
  split; dsimp,
  { intros i j k, simp only [neg_comp, comp_neg, neg_neg], apply h1 },
  { intros i j hij, rw neg_eq_zero, apply h2,
    intro H, apply hij,
    cases cov; dsimp [coherent_indices] at H ⊢; apply (succ_equiv ι).injective; exact H }
end

lemma shift_d (C : complex_like ι V cov) (i j : ι) :
  ((shift _ _).obj C).d i j = -C.d (succ i) (succ j) :=
rfl

instance shift.additive : (shift ι V : complex_like ι V cov ⥤ complex_like ι V cov).additive :=
{ map_zero' :=
  by { rintro ⟨⟩ ⟨⟩, ext, dsimp [shift], simp only [category.id_comp, category.comp_id], refl },
  map_add' :=
  by { rintro ⟨⟩ ⟨⟩ f g, ext, dsimp [shift], simp only [category.id_comp, category.comp_id] } }

-- this is a major pain, but we might not need it
-- instance : has_shift (differential_object.complex_like ι V cov) :=
-- { shift := differential_object.lift_equivalence (category_theory.shift _) $ λ X,
--   begin
--     admit
--   end }

end complex_like

end differential_object

section

variables (ι V) [has_succ ι] [category V] [has_zero_morphisms V]

abbreviation cochain_complex := differential_object.complex_like ι V tt
abbreviation chain_complex := differential_object.complex_like ι V ff

end

namespace cochain_complex

variables {ι V} [decidable_eq ι] [has_succ ι] [category V] [has_zero_morphisms V]

/-
Constructor of a `cochain_complex` from the usual data which a mathematician
would regard as giving a cochain complex (maps Xᵢ → X_{i+1}) with d^2=0)
to what Lean regards as a cochain complex internally (which is of no relevance).
-/
@[simps]
def mk' (X : ι → V) (d : Π i, X i ⟶ X (succ i)) (h : ∀ i, d i ≫ d (succ i) = 0) :
  cochain_complex ι V :=
{ X := X,
  d := λ i j, if h : succ i = j then d i ≫ eq_to_hom (congr_arg _ h) else 0,
  d_comp_d := λ i j k,
  begin
    split_ifs with h1 h2,
    { subst k, subst j, simp only [category.comp_id, eq_to_hom_refl, h] },
    all_goals { simp only [zero_comp, comp_zero] }
  end,
  d_eq_zero := λ i j hij, dif_neg hij }

@[simp] lemma mk'_d' (X : ι → V) (d : Π i, X i ⟶ X (succ i))
  (h : ∀ i, d i ≫ d (succ i) = 0) (i : ι) :
  (mk' X d h).d i (succ i) = d i := -- not `rfl` -- hard luck.
  -- Our `d i j` function needs a proof that `j = succ i`
  -- so and we need to run a `dif_pos` on it.
calc (mk' X d h).d i (succ i)
    = d i ≫ eq_to_hom (congr_arg _ rfl) : dif_pos rfl
... = d i : by simp only [category.comp_id, eq_to_hom_refl]

end cochain_complex
/-

It's limits v colimits round two, and this time it's equally tedious.
All the constructions we just did for cochain complexes we will now
do again for chain complexes.
-/
namespace chain_complex

variables {ι V} [decidable_eq ι] [has_succ ι] [category V] [has_zero_morphisms V]

@[simps]
def mk' (X : ι → V) (d : Π i, X (succ i) ⟶ X i) (h : ∀ i, d (succ i) ≫ d i = 0) :
  chain_complex ι V :=
{ X := X,
  d := λ i j, if h : i = succ j then eq_to_hom (congr_arg _ h) ≫ d j else 0,
  d_comp_d := λ i j k,
  begin
    split_ifs with h1 h2,
    { subst i, subst j, simp only [category.id_comp, eq_to_hom_refl, h] },
    all_goals { simp only [zero_comp, comp_zero] }
  end,
  d_eq_zero := λ i j hij, dif_neg hij }

@[simp] lemma mk'_d' (X : ι → V) (d : Π i, X (succ i) ⟶ X i)
  (h : ∀ i, d (succ i) ≫ d i = 0) (i : ι) :
  (mk' X d h).d (succ i) i = d i :=
calc (mk' X d h).d (succ i) i
    = eq_to_hom (congr_arg _ rfl) ≫ d i : dif_pos rfl
... = d i : by simp only [category.id_comp, eq_to_hom_refl]

end chain_complex

namespace category_theory

variables {ι} {V₁ V₂ : Type*} [category V₁] [category V₂]

section has_zero_morphisms
variables [has_zero_morphisms V₁] [has_zero_morphisms V₂]

@[simps]
def functor.map_differential_object (F : V₁ ⥤ V₂) :
  differential_object ι V₁ ⥤ differential_object ι V₂ :=
{ obj := λ C,
  { X := λ i, F.obj (C.X i),
    d := λ i j, F.map (C.d i j) },
  map := λ C₁ C₂ f,
  { f := λ i, F.map (f.f i),
    comm := λ i j, by simp only [← F.map_comp, f.comm] },
  map_id' := by { intros, ext, exact F.map_id _ },
  map_comp' := by { intros, ext, exact F.map_comp _ _ } }

@[simps]
def functor.map_complex_like' [has_succ ι] (F : V₁ ⥤ V₂) (hF : ∀ x y, F.map (0 : x ⟶ y) = 0) :
  differential_object.complex_like ι V₁ cov ⥤ differential_object.complex_like ι V₂ cov :=
{ obj := λ C,
  { X := λ i, F.obj (C.X i),
    d := λ i j, F.map (C.d i j),
    d_comp_d := λ _ _ _, by simp only [← F.map_comp, C.d_comp_d, hF],
    d_eq_zero := λ _ _ h, by simp only [C.d_eq_zero h, hF] },
  map := λ C₁ C₂ f, (F.map_differential_object.map f),
  map_id' := by { intros, ext, exact F.map_id _ },
  map_comp' := by { intros, ext, exact F.map_comp _ _ } }

end has_zero_morphisms

section preadditive
variables [preadditive V₁] [preadditive V₂]

@[simps]
def functor.map_complex_like [has_succ ι] (F : V₁ ⥤ V₂) [F.additive] :
  differential_object.complex_like ι V₁ cov ⥤ differential_object.complex_like ι V₂ cov :=
F.map_complex_like' $ λ x y, functor.additive.map_zero

end preadditive

end category_theory
