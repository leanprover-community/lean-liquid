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
| 0 1 2 rfl rfl := h
| (i+1) _ _ rfl rfl := C.d_comp_d _ _ _

def cons (C : cochain_complex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) (h : d ≫ C.d 0 1 = 0) :
  cochain_complex 𝓐 ℕ :=
{ X := cons.X C A,
  d := cons.d C A d,
  shape' := cons.shape C A d,
  d_comp_d' := cons.d_comp_d C A d h }

section simp_lemmas

variables (C : cochain_complex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) (h : d ≫ C.d 0 1 = 0)

@[simp] lemma cons_X_0 : (C.cons A d h).X 0 = A := rfl
@[simp] lemma cons_X_succ (n : ℕ) : (C.cons A d h).X (n+1) = C.X n := rfl
@[simp] lemma cons_d_01 : (C.cons A d h).d 0 1  = d := rfl
@[simp] lemma cons_d_succ (n : ℕ) : (C.cons A d h).d (n+1) (n+2) = C.d n (n+1) := rfl

end simp_lemmas

namespace hom

variables {C₁ C₂ : cochain_complex 𝓐 ℕ} {A₁ A₂ : 𝓐}
  {d₁ : A₁ ⟶ C₁.X 0} {d₂ : A₂ ⟶ C₂.X 0}
  (h₁ : d₁ ≫ C₁.d 0 1 = 0) (h₂ : d₂ ≫ C₂.d 0 1 = 0)
  (f : A₁ ⟶ A₂) (g : C₁ ⟶ C₂)

def cons.f : Π (i : ℕ), (C₁.cons A₁ d₁ h₁).X i ⟶ (C₂.cons A₂ d₂ h₂).X i
| 0 := f
| (i+1) := g.f i

lemma cons.comm (w : f ≫ d₂ = d₁ ≫ g.f 0) :
  ∀ (i j : ℕ), (complex_shape.up ℕ).rel i j →
    cons.f h₁ h₂ f g i ≫ (C₂.cons A₂ d₂ h₂).d i j = (C₁.cons A₁ d₁ h₁).d i j ≫ cons.f h₁ h₂ f g j
| 0 1 rfl := w
| (i+1) _ rfl := g.comm i (i+1)

def cons (w : f ≫ d₂ = d₁ ≫ g.f 0) : C₁.cons A₁ d₁ h₁ ⟶ C₂.cons A₂ d₂ h₂ :=
{ f := cons.f h₁ h₂ f g,
  comm' := cons.comm h₁ h₂ f g w }

section simp_lemmas

variables (w : f ≫ d₂ = d₁ ≫ g.f 0)

@[simp] lemma cons_f_0 : (cons h₁ h₂ f g w).f 0 = f := rfl
@[simp] lemma cons_f_succ (i : ℕ) : (cons h₁ h₂ f g w).f (i+1) = g.f i := rfl

end simp_lemmas

end hom

end cochain_complex
