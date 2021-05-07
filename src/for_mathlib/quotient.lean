import data.quot
import data.setoid.basic

-- PR together with data_setoid_partition

--- in data.quot
lemma quotient.mk_eq_iff_out {α : Type*} [s : setoid α] {x : α} {y : quotient s} : ⟦x⟧ = y ↔ x ≈ quotient.out y :=
begin
  split,
  { intros h,
    symmetry,
    have := quotient.mk_out x,
    rwa h at this },
  { intro h,
    rw ← quotient.out_eq y,
    exact quotient.sound h }
end

-- in data.setoid.basic
lemma setoid.comm {α : Type*} (s : setoid α) {x y} : s.rel x y ↔ s.rel y x :=
⟨λ h, setoid.symm h, λ h, setoid.symm h⟩
