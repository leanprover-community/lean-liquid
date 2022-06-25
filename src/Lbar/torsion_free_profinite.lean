import for_mathlib.Profinite.extend
import Lbar.basic
import Lbar.functor

universe u

open_locale nnreal

variables (r' : ℝ≥0) [fact (0 < r')]
variable {S : Profinite.{u}}

set_option pp.universes true

open Lbar Profinite

lemma torsion_free_profinite (n : ℤ) (x : (extend (Fintype_Lbar.{u u} r')).obj S) :
  n • x = 0 → n = 0 ∨ x = 0:=
begin
  intro hx,
  dsimp at x,
  sorry,
end

instance : no_zero_smul_divisors ℤ ((extend (Fintype_Lbar.{u u} r')).obj S) :=
begin
  fconstructor,
  intros c x hx,
  apply torsion_free_profinite r' c x hx,
end
