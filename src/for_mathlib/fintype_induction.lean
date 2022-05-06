import data.fintype.basic
import category_theory.Fintype

open_locale classical

universe u

-- This is an awkward hybrid: we should state the induction principle for unbundled fintype
-- and then if it is necessary provide an interface for using it with `Fintype`.

lemma Fintype.induction_empty_sum {P : Fintype.{u} → Prop}
  (of_equiv : ∀ {α β : Fintype.{u}}, α ≃ β → P α → P β)
  (h_empty : P (Fintype.of pempty))
  (h_option : ∀ {α : Fintype.{u}}, P α → P (Fintype.of (α ⊕ (punit : Type u))))
  (α : Fintype.{u}) : P α :=
begin
  let Q : Π (α : Type u) [fintype α], Prop := λ a h, P ⟨a,h⟩,
  have H := @fintype.induction_empty_option' Q _ _ _ α α.str,
  { cases α, exact H },
  { introsI α β _ e h,
    haveI : fintype α := fintype.of_equiv _ e.symm,
    let e' : Fintype.of α ≃ Fintype.of β := e,
    apply of_equiv e',
    convert h },
  { assumption },
  { introsI α _ h,
    let e : option α ≃ α ⊕ (punit : Type u) := equiv.option_equiv_sum_punit _,
    let e' : Fintype.of (option α) ≃ Fintype.of (α ⊕ punit) := e,
    apply of_equiv e'.symm,
    exact h_option h }
end
