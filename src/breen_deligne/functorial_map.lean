import breen_deligne.universal_map

/-

This file is a big slow mess

/-!

# Universality of universal maps

(Note: this file exists as a consistency check, but is not used in the rest of the project.)

A `universal_map m n` in this repo is a finite formal `ℤ`-linear combination
of `m × n` matrices (so-called `basic_universal_map`s). In this file we show that
to give a term of this type is to give a term of type `functorial_map m n`, which is
defined to be a collection of additive group homomorphisms `ℤ[A^m] →+ ℤ[A^n]`
for each abelian group `A`, functorial in `A`.

The dictionary: given an `m × n` matrix with integer coefficients,
it induces a map `A^m → A^n` in the obvious way and hence a group
homomorphism `ℤ[A^m] →+ ℤ[A^n]`; hence finite formal integer
combinations of these also give group homomorphisms.
It is not hard to check that homomorphisms obtained in this way are
functorial in `A`.

Conversely, we start by identifying `(ℤ^p)^q` with `q × p` matrices in
the obvious way. Now given a functorial collection of homomorphisms `ℤ[A^m] → ℤ[A^n]`,
evaluating at collection at the group `A=ℤ^m` and the element of `(ℤ^m)^m`
corresponding to the `m × m` identity matrix gives an element of `ℤ[(ℤ^m)^n]` which
can be thought of in a natural way as a finite ℤ-linear combination of
`m × n` matrices.

The proofs that these constructions are inverse to one another is relatively
straightforward, and is of course given in full below. To show that the
construction `functorial_map m n → universal_map m n → functorial_map m n`
is the identity, we observe that the value of a `functorial_map m n` at
an element `x : A^m` can be computed by using functoriality applied
to the map `ℤ^m → A` sending the i'th basis vector to `x i`.

-/

noncomputable theory

-- get some notation working:
open_locale big_operators direct_sum

local attribute [instance] type_pow
local notation `ℤ[` A `]` := free_abelian_group A

universes u

namespace breen_deligne

section functorial_map_section

open free_abelian_group

/-- A term `F : functorial_map m n` is a collection of group homomorphisms
  `F.f A : ℤ[A^m] →+ ℤ[A^n]`, functorial in the abelian group `A`. -/
@[ext] structure functorial_map (m n : ℕ) :=
(f (A : Type u) [add_comm_group A] : ℤ[A^m] →+ ℤ[A^n])
(functorial {A : Type u} [add_comm_group A] {B : Type u} [add_comm_group B] (φ : A →+ B) :
  (free_abelian_group.map (φ.pow n)).comp (f A) = (f B).comp (map (φ.pow m)))

variables {m n : ℕ}

namespace functorial_map

open add_monoid_hom

def add (F G : functorial_map m n) : functorial_map m n :=
{ f := λ A _, by exactI F.f A + G.f A,
  functorial := λ A _ B _ φ, by rw [comp_add, add_comp, F.functorial, G.functorial] }

instance : has_add (functorial_map m n) := ⟨add⟩

def zero : functorial_map m n :=
{ f := λ A _, 0,
  functorial := by intros; simp }

instance : has_zero (functorial_map m n) := ⟨zero⟩

def neg (F : functorial_map m n) : functorial_map m n :=
{ f := λ A _, by exactI -F.f A,
  functorial := λ A _ B _ φ, by rw [comp_neg, neg_comp, F.functorial]}

instance : has_neg (functorial_map m n) := ⟨neg⟩

instance : add_comm_group (functorial_map m n) :=
{ add := (+),
  add_assoc := λ _ _ _, ext _ _ $ funext (λ A, funext (λ _, by exactI add_assoc _ _ _)),
  zero := 0,
  zero_add := λ _, ext _ _ $ funext (λ A, funext (λ _, by exactI zero_add _)),
  add_zero := λ _, ext _ _ $ funext (λ A, funext (λ _, by exactI add_zero _)),
  neg := has_neg.neg,
  add_left_neg := λ _, ext _ _ $ funext (λ A, funext (λ _, by exactI add_left_neg _)),
  add_comm := λ F G, ext _ _ $ funext (λ A, funext (λ _, by exactI add_comm _ _)) }

end functorial_map

end functorial_map_section

section punit_stuff

open free_abelian_group

-- this is now on `free-abelian-group-equivs` branch
def punit_equiv : ℤ[punit] ≃+ ℤ :=
{ inv_fun := λ n, n • of (punit.star),
  to_fun := free_abelian_group.lift (λ _, (1 : ℤ)),
  left_inv := λ z, free_abelian_group.induction_on z
    (by {dsimp only, rw [add_monoid_hom.map_zero, zero_smul]})
    (λ x, punit.cases_on x (by simp))
    (λ x, punit.cases_on x (by simp))
    (λ x y hx hy, by { simp only [add_monoid_hom.map_add, add_smul] at *, rw [hx, hy]}),
  right_inv := λ n, by { rw [add_monoid_hom.map_zsmul, lift.of], exact zsmul_int_one n},
  map_add' := add_monoid_hom.map_add _ }

-- this is now on `free-abelian-group-equivs` branch
def equiv_of_equiv {α β : Type*} (f : α ≃ β) : free_abelian_group α ≃+ free_abelian_group β :=
{ to_fun := free_abelian_group.lift $ free_abelian_group.of ∘ f,
  inv_fun := free_abelian_group.lift $ free_abelian_group.of ∘ f.symm,
  left_inv := begin
    intros x,
    refine free_abelian_group.induction_on x
    (by simp only [add_monoid_hom.map_zero])
    (by simp only [equiv.symm_apply_apply, eq_self_iff_true, function.comp_app, lift.of, forall_true_iff])
    (by simp only [equiv.symm_apply_apply, eq_self_iff_true, function.comp_app,
      add_monoid_hom.map_neg, lift.of, forall_true_iff]) _,
    intros x y h,
    simp only [h, imp_self, add_right_inj, add_monoid_hom.map_add],
  end,
  right_inv := begin
    intros x,
    refine free_abelian_group.induction_on x
    (by simp only [add_monoid_hom.map_zero])
    (by simp only [eq_self_iff_true, function.comp_app, equiv.apply_symm_apply, lift.of, forall_true_iff])
    (by simp only [eq_self_iff_true, function.comp_app, equiv.apply_symm_apply,
      add_monoid_hom.map_neg, lift.of, forall_true_iff]) _,
    intros x y h,
    simp only [h, imp_self, add_right_inj, add_monoid_hom.map_add],
  end,
  map_add' := begin
     intros x y,
     simp only [add_monoid_hom.map_add],
  end }

end punit_stuff

lemma lift_smul_eq_lift {A : Type*} [add_comm_group A] (a : A) (c : ℤ[punit]) :
  (free_abelian_group.lift (λ _, (1 : ℤ))) c • a = free_abelian_group.lift (λ _, a) c :=
begin
  rw ← punit_equiv.left_inv c,
  generalize : punit_equiv.to_fun c = d,
  delta punit_equiv, dsimp only,
  apply int.induction_on d,
  { simp },
  { intros i hi,
    simp only [add_smul, ←hi, free_abelian_group.lift.of,
      add_monoid_hom.map_add, add_left_inj, one_zsmul], },
  { intros i hi,
    simp only [add_monoid_hom.map_neg, neg_inj, int.cast_neg, neg_smul, int.cast_sub] at *,
    simp only [sub_smul, ←hi, free_abelian_group.lift.of, one_zsmul,
      add_monoid_hom.map_neg, add_monoid_hom.map_sub, neg_inj, neg_smul, sub_left_inj] }
end

namespace universal_map
open add_monoid_hom

@[simps]
def to_functorial_map {m n : ℕ} (U : universal_map m n) :
  functorial_map.{u} m n :=
{ f := λ A _, by exactI eval A U,
  functorial :=
  λ A _ B _ φ, begin
    -- The proof that evaluation of universal maps is functorial for group homomorphisms.
    -- We start by unravelling what the question is.
    resetI,
    ext as,
    rw [comp_apply, comp_apply],
    -- free_abelian_group.map_of should be redefined now map is an add_group_hom not a map?
    -- Bhavik says make a dsimp lemma, I say make `map_of_apply` or `map_apply`
    change _ = ((eval B) U) ((φ.pow m) <$> (free_abelian_group.of as)),
    rw free_abelian_group.map_of,
    --  We need to prove that for all `as : A^m`, evaluating `U` then mapping with `φ`
    -- is the same as applying `φ` and then evaluating `U` on the corresponding element of
    -- `ℤ[B^m]`.
    -- By linearity, we can assume that `U` is a basic universal map `f`.
    apply free_abelian_group.induction_on U,
    { simp only [map_zero, zero_apply]},
    { intro f,
      -- Here is the proof for basic universal maps.
      simp only [basic_universal_map.eval_of, eval_of],
      -- We use the universal property
      convert free_abelian_group.map_of _ _,
      -- which boils the question down to checking that φ : A^n → B^n and φ : A^m → B^m
      -- commutes with the matrix action A^m → A^n
      ext i,
      -- and this just boils down to trivialities
      simp only [basic_universal_map.pre_eval_apply, pow_eval, add_monoid_hom.map_sum,
        map_zsmul], },
      -- the rest is just checking that the question about universal maps was linear
      -- so the reduction to the basic case was OK.
    { intros F hF,
      simp only [add_monoid_hom.map_neg, neg_inj, neg_apply, hF] },
    { intros F G hF hG, simp only [hF, hG, add_monoid_hom.map_add, add_apply]}
  end }

def from_functorial_map {m n : ℕ} (F : functorial_map.{u} m n) :
  universal_map m n :=
free_abelian_group.lift
  (λ x, free_abelian_group.of
    (λ i j, (punit_equiv ((x : (ℤ[punit] ^ m) ^ n) i j)) : basic_universal_map m n))
  (F.f
  -- We evaluate on ℤ^m (in universe `u`)
    (free_abelian_group (punit)^m)
  -- and on the identity matrix.
    (free_abelian_group.of (λ i j, if i = j then free_abelian_group.of punit.star else 0)))

lemma to_functorial_map_from_functorial_map
  {m n : ℕ} (F : functorial_map.{u} m n) :
  to_functorial_map (from_functorial_map F) = F :=
begin
  -- We check the two functorial maps agree on the abelian group `A` and on input `x : A^m`
  ext A inst x, resetI,
  -- Let φ be the map from ℤ^m to A sending the i'th basis vector to `x i`.
  let φ : ℤ[punit.{u+1}]^m →+ A := pow_hom (λ i, free_abelian_group.lift (λ _, x i)),
  -- Use the fact that the original functorial map is functorial for `φ`, and
  -- evaluate the corresponding commutative diagram at the identity matrix in `(ℤ^m)^m`.
  have h := F.functorial φ,
  set id_mat : (ℤ[punit]^m)^m :=
    λ i j, if i = j then free_abelian_group.of punit.star else 0,
  replace h := congr_fun h (free_abelian_group.of id_mat),
  -- The corresponding equation is almost what we have to prove.
  simp only [free_abelian_group.map_of_apply, function.comp_app, coe_comp] at h,
  convert h using 3,
  { clear h,
    -- Of the two things left to do, the first follows from the following assertion
    -- (letting t be the image of the identity map under φ)
    dsimp only [from_functorial_map, to_functorial_map],
    generalize : (F.f (ℤ[punit] ^ m)) (free_abelian_group.of id_mat) = t,
    -- show eval A (free_abelian_group.lift
    --   (λ (y : fin n → fin m → ℤ[punit]),
    --     free_abelian_group.of (λ (i : fin n) (j : fin m), punit_equiv (y i j))) _)
    --       (free_abelian_group.of x) = _,
    -- and by linearity this assertion only needs to be verified for `t` an `m × n`
    -- matrix (rather than a ℤ-linear combination of them)
    apply free_abelian_group.induction_on t,
    { simp only [map_zero, zero_apply]},
    { clear t, intro t,
      -- for which it follows by unravelling the definitions.
      rw free_abelian_group.lift.of,
      rw eval_of,
      convert (free_abelian_group.map_of _ _).symm,
      rw free_abelian_group.map_of,
      convert free_abelian_group.map_of _ _,
      ext i,
      simp only [φ, pow_hom, add_monoid_hom.pow, basic_universal_map.pre_eval_apply],
      apply finset.sum_congr rfl,
      rintro j -,
      apply lift_smul_eq_lift },
    { simp only [imp_self, forall_const, neg_inj, map_neg, neg_apply]},
    { intros x y hx hy, simp * at * } },
  { -- The second and final thing we need to check is that evaluating `φ` on
    -- the identity matrix gives us `x`, and this follows essentially immediately
    -- from the definitions.
    ext i,
    simp only [id_mat, add_monoid_hom.pow, φ, pow_hom, coe_mk, function.comp_app],
    convert (finset.sum_ite_eq (finset.univ : finset (fin m)) i x).symm using 2,
    { rw if_pos (finset.mem_univ _) },
    ext j,
    split_ifs; simp only [free_abelian_group.lift.of, map_zero] },
end

-- set_option pp.universes true

lemma from_functorial_map_to_functorial_map
  {m n : ℕ} (U : universal_map m n) :
  from_functorial_map (to_functorial_map U) = U :=
begin
  dsimp only [from_functorial_map, to_functorial_map],
  -- By linearity it suffices to check for basic universal maps.
  apply free_abelian_group.induction_on U,
  { simp only [map_zero, zero_apply] },
  { intro b,
    -- so let b be a basic universal map. Now unravel everything
    simp only [free_abelian_group.lift.of, basic_universal_map.eval_of, eval_of,
      basic_universal_map.pre_eval_apply],
    congr',
    ext i j',
    -- and it boils down to checking that a sum over j of `b i j` times `delta j j'` is b i j'.
    convert punit_equiv.right_inv (b i j'),
    simp only [add_equiv.neg_fun_eq_symm, add_equiv.to_fun_eq_coe, add_equiv.apply_symm_apply, zsmul_eq_mul],
    apply _root_.congr_arg,
    change _ = (b i j') • _,
    rw @fintype.sum_apply (fin m) _ (fin m) _ _ j'
      (λ j, b i j • (λ (j_1 : fin m), ite (j = j_1) (free_abelian_group.of punit.star) 0)),
    dsimp,
    simp only [finset.mem_univ, if_true, finset.sum_ite_eq', zsmul_eq_mul, mul_ite, mul_zero], },
  { simp },
  { intros u v hu hv,
    simp * at * }
end

/-- universal maps are equivalent to functorial maps. -/
@[simps]
def universal_map_equiv_functorial_map (m n : ℕ) : universal_map m n ≃+ functorial_map.{u} m n :=
{ -- The construction of a functorial map from a universal map.
  to_fun := λ U, to_functorial_map U,
  -- The construction of a universal map from a functorial map
  inv_fun := λ F, from_functorial_map F,
  -- We check that given a universal map, constructing a functorial map and then
  -- another universal map gives us the universal map we started with.
  left_inv := from_functorial_map_to_functorial_map,
  -- Finally we check that starting with a functorial map and then constructing the
  -- universal map and then the functorial map gets us back to where we started.
  right_inv := to_functorial_map_from_functorial_map,
  -- Note finally that this functorial constuction is an isomorphism of
  -- abelian groups, as can be easily checked.
  map_add' := begin
    intros u v,
    ext,
    resetI,
    simp,
    refl,
  end }

@[ext] lemma to_functorial_map_inj {m n : ℕ} (f g : universal_map m n)
  (h : to_functorial_map.{0} f = to_functorial_map.{0} g) :
  f = g :=
(universal_map_equiv_functorial_map m n).injective h

end universal_map

end breen_deligne

-/
