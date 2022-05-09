import algebra.homology.homological_complex

open category_theory

namespace cochain_complex

variables {𝓐 : Type*} [category 𝓐] [preadditive 𝓐]

def cons.X (C : cochain_complex 𝓐 ℕ) (A : 𝓐) : ℕ → 𝓐
| 0     := A
| (n+1) := C.X n

def cons.d (C : cochain_complex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) :
  Π (i j : ℕ), cons.X C A i ⟶ cons.X C A j
| 0 0     := 0
| 0 1     := d
| 0 (j+2) := 0
| (i+1) 0 := 0
| (i+1) (j+1) := C.d i j

lemma cons.shape (C : cochain_complex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) :
  ∀ (i j : ℕ), ¬(complex_shape.up ℕ).rel i j → cons.d C A d i j = 0
| 0 0     h := rfl
| 0 1     h := (h rfl).elim
| 0 (j+2) h := rfl
| (i+1) 0 h := rfl
| (i+1) (j+1) h := C.shape i j $ mt (add_left_inj 1).mpr h

lemma cons.d_comp_d (C : cochain_complex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) (h : d ≫ C.d 0 1 = 0) :
  ∀ i j k, (complex_shape.up ℕ).rel i j → (complex_shape.up ℕ).rel j k →
    cons.d C A d i j ≫ cons.d C A d j k = 0
| 0 1 2 rfl rfl := sorry
| (i+1) _ _ rfl rfl := sorry

def cons (C : cochain_complex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) (h : d ≫ C.d 0 1 = 0) :
  cochain_complex 𝓐 ℕ :=
{ X := cons.X C A,
  d := cons.d C A d,
  shape' := cons.shape C A d,
  d_comp_d' := sorry }

end cochain_complex
