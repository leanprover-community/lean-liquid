import topology.constructions

/-
In this file, we define notation `X^n` to take powers of types.
By definition, `X^n` is modelled as functions from `fin n` to `X`.
-/

/-- A definition of powers of a type. -/
def type_pow : has_pow (Type*) ℕ := ⟨λ A n, fin n → A⟩


namespace type_pow_topology

local attribute [instance] type_pow

variables (z : ℤ) (A : Type) [add_comm_group A] (n : ℕ) (x : A^n)
example : add_comm_group (fin n → A) := by show_term {apply_instance}


instance topological_space {n : ℕ} {α : Type*} [topological_space α] : topological_space (α^n) :=
  Pi.topological_space

--instance {n : ℕ} {α : Type*} [topological_space α] [discrete_topology α] : discrete_topology (α^n) := sorry

end type_pow_topology

namespace add_monoid_hom

universes u v

local attribute [instance] type_pow

/-- The group homomorphism `A^n →+ B^n` induced by a group homomorphism `A →+ B`. -/
def pow {A : Type u} [add_comm_group A] {B : Type u} [add_comm_group B]
  (φ : A →+ B) (n : ℕ) : A^n →+ B^n :=
{ to_fun := (∘) φ,
  map_zero' := funext (λ _, φ.map_zero),
  map_add' := λ _ _, funext (λ _, φ.map_add _ _) }

lemma pow_eval {A : Type u} [add_comm_group A] {B : Type u} [add_comm_group B]
  (φ : A →+ B) (n : ℕ) (as : A ^ n) (i : fin n) : φ.pow n as i = φ (as i) := rfl

open_locale big_operators

/-- The group homomorphism `A^n →+ B` induced by `n` group homs `A →+ B` -/
def pow_hom {A : Type u} [add_comm_group A] {B : Type u} [add_comm_group B]
  {n : ℕ} (φ : fin n → A →+ B) : (A^n →+ B) :=
{ to_fun := λ z, ∑ (i : fin n), φ i (z i),
  map_zero' := by simp only [pi.zero_apply, finset.sum_const_zero, map_zero],
  map_add' := λ x y, begin
    rw [← finset.sum_add_distrib],
    simp,
  end }

end add_monoid_hom

local attribute [instance] type_pow

/-- The natural bijection `(A^m)^n ≃ (A^n)^m`. -/
def pow_pow {A : Type*} {m n : ℕ} : (A^m)^n ≃ (A^n)^m :=
{ to_fun := λ f i j, f j i,
  inv_fun := λ f j i, f i j,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl }

/-- The natural bijection `A^n ≃ B^n` induced by a bijection `A ≃ B`.-/
def pow_equiv {A B : Type*} (e : A ≃ B) {n : ℕ} : A^n ≃ B^n :=
{ to_fun := λ f i, e (f i),
  inv_fun := λ g i, e.symm (g i),
  left_inv := λ f, funext (λ i, equiv.symm_apply_apply _ _),
  right_inv := λ g, funext (λ i, equiv.apply_symm_apply _ _) }

#lint- only unused_arguments def_lemma doc_blame
