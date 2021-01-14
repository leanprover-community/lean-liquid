-- import data.polynomial
-- import data.mv_polynomial
-- import ring_theory.ideal.operations

-- universe variables u

-- constant laurent_polynomial (R : Type u) : Type u

-- namespace laurent_polynomial
-- open polynomial mv_polynomial
-- variables (R : Type u) [comm_ring R]

-- @[instance]
-- constant comm_ring : comm_ring (laurent_polynomial R)

-- variables {R}

-- constant of_polynomial : polynomial R → laurent_polynomial R

-- constant of_inv_polynomial : polynomial R → laurent_polynomial R

-- lemma of_polynomial_X_mul_of_inv_polynomial_X :
--   of_polynomial (X : polynomial R) * of_inv_polynomial X = 1 := sorry

-- constant as_quotient : mv_polynomial bool R →+* laurent_polynomial R

-- lemma as_quotient_surjective :
--   function.surjective (@as_quotient R _) :=
-- sorry

-- lemma as_quotient_ker :
--   (@as_quotient R _).ker = ideal.span {X tt * X ff - 1} := sorry

-- end laurent_polynomial
