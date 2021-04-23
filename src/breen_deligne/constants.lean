import breen_deligne.suitable

open_locale nnreal

namespace breen_deligne

namespace data

variables (BD : data) (r r' : ℝ≥0)

/-- Example of a very suitable sequence of constants for given Breen--Deligne data. -/
def c_ (BD : data) (r r' : ℝ≥0) : ℕ → ℝ≥0
| 0     := 1
| (n+1) := sorry

instance c_very_suitable : BD.very_suitable r r' (BD.c_ r r') :=
{ universal_very_suitable :=
  begin
    intros i j,
    sorry
  end }

end data

namespace package

variables (BD : package) (r r' : ℝ≥0)

/-- Example of an adept sequence of constants for
a given Breen--Deligne package `BD` and constants `c_`. -/
def c' (BD : package) (c_ : ℕ → ℝ≥0) : ℕ → ℝ≥0 :=
sorry

instance c'_adept (c_ : ℕ → ℝ≥0) : package.adept BD c_ (c' BD c_) :=
sorry

end package

end breen_deligne
