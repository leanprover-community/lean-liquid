-- import algebra.group.basic
-- import linear_algebra.basis
-- import linear_algebra.invariant_basis_number

-- noncomputable theory

-- -- TODO: most of this file should just be about fin.gen. free modules over some ring.

-- /-- A *lattice* is a free abelian group of finite rank. -/
-- class Lattice (Λ : Type*) extends add_comm_group Λ :=
-- (exists_finite_basis : ∃ {ι : Type} [fintype ι] (v : ι → Λ), is_basis ℤ v)

-- namespace Lattice
-- variables (Λ : Type*) [Lattice Λ]

-- /-- The *rank* of a lattice is the cardinality of an arbitrary basis. -/
-- def rank : ℕ :=
-- @fintype.card (classical.some (@exists_finite_basis Λ _))
--   (classical.some $ classical.some_spec $ (@exists_finite_basis Λ _))

-- lemma card_basis_eq_rank (ι : Type*) [fintype ι] (v : ι → Λ) (h : is_basis ℤ v) :
--   fintype.card ι = rank Λ :=
-- sorry
-- -- use: invariant_basis_number ℤ

-- end Lattice
