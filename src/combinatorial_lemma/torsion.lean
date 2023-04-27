import combinatorial_lemma.lem97
import algebra.module.torsion
import linear_algebra.free_module.pid

variables {Λ : Type*} [add_comm_group Λ]
variable {ι : Type*}

open submodule (torsion)

namespace combinatorial_lemma

lemma torsion_le_ker (f : Λ →+ ℤ) :
  torsion ℤ Λ ≤ linear_map.ker f.to_int_linear_map :=
begin
  rintro l ⟨⟨n, hn⟩, hl⟩,
  apply_fun f at hl,
  change f (n • l) = f 0 at hl,
  simp only [map_zero, map_zsmul, algebra.id.smul_eq_mul] at hl,
  rwa mul_left_mem_non_zero_divisors_eq_zero_iff hn at hl,
end

def aux_equiv : ((Λ ⧸ torsion ℤ Λ) →+ ℤ) ≃+ (Λ →+ ℤ) :=
{ inv_fun := λ f, (submodule.liftq (torsion ℤ Λ) f.to_int_linear_map (torsion_le_ker f)).to_add_monoid_hom,
  left_inv := λ f, by ext l : 2; refl,
  right_inv := λ f, by { ext l : 2, refl },
  .. add_monoid_hom.comp_hom' (submodule.mkq _).to_add_monoid_hom }

/-- Lemma 9.7 of [Analytic]. See also the (mathematically indistinguishable) variant `lem97`. -/
lemma lem97'' [fintype ι] [module.finite ℤ Λ] (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x₀ ∈ A) (y : Λ →+ ℤ),
    x = N • y + x₀ ∧
    ∀ i, (x (l i)).nat_abs = N * (y (l i)).nat_abs + (x₀ (l i)).nat_abs :=
begin
  let Λ' := Λ ⧸ torsion ℤ Λ,
  let l' : ι → Λ' := submodule.quotient.mk ∘ l,
  haveI : module.finite ℤ Λ' := module.finite.of_surjective (submodule.mkq _) (submodule.quotient.mk_surjective _),
  obtain ⟨n, hn⟩ := @module.free_of_finite_type_torsion_free' ℤ _ _ _ Λ' _ _ _ _,
  haveI : module.free ℤ Λ' := module.free.of_basis hn,
  obtain ⟨A', hA'⟩ := lem97' N hN l',
  classical,
  let φ : (Λ' →+ ℤ) ≃+ (Λ →+ ℤ) := aux_equiv,
  let A : finset (Λ →+ ℤ) := finset.image φ A',
  use A,
  intro x,
  let x' := φ.symm x,
  obtain ⟨x'₀, hx'₀, y₀, h₁, h₂⟩ := hA' x',
  refine ⟨φ x'₀, finset.mem_image_of_mem _ hx'₀, φ y₀, _, λ i, h₂ i⟩,
  apply_fun φ at h₁, simpa only [add_equiv.apply_symm_apply, map_add, map_nsmul] using h₁,
end

end combinatorial_lemma
