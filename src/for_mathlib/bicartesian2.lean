import for_mathlib.chain_complex_cons
import for_mathlib.mapping_cone
import for_mathlib.exact_seq3
import for_mathlib.commsq
import for_mathlib.complex_extend
import for_mathlib.derived.K_projective

noncomputable theory

open category_theory category_theory.limits

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

variables {A₁₁ A₁₂ A₁₃ A₁₄ A₁₅ : 𝓐}
variables {A₂₁ A₂₂ A₂₃ A₂₄ A₂₅ : 𝓐}
variables {A₃₁ A₃₂ A₃₃ A₃₄ A₃₅ : 𝓐}
variables {A₄₁ A₄₂ A₄₃ A₄₄ A₄₅ : 𝓐}
variables {A₅₁ A₅₂ A₅₃ A₅₄ A₅₅ : 𝓐}

variables {f₁₁ : A₁₁ ⟶ A₁₂} {f₁₂ : A₁₂ ⟶ A₁₃} {f₁₃ : A₁₃ ⟶ A₁₄} {f₁₄ : A₁₄ ⟶ A₁₅}
variables {g₁₁ : A₁₁ ⟶ A₂₁} {g₁₂ : A₁₂ ⟶ A₂₂} {g₁₃ : A₁₃ ⟶ A₂₃} {g₁₄ : A₁₄ ⟶ A₂₄} {g₁₅ : A₁₅ ⟶ A₂₅}
variables {f₂₁ : A₂₁ ⟶ A₂₂} {f₂₂ : A₂₂ ⟶ A₂₃} {f₂₃ : A₂₃ ⟶ A₂₄} {f₂₄ : A₂₄ ⟶ A₂₅}
variables {g₂₁ : A₂₁ ⟶ A₃₁} {g₂₂ : A₂₂ ⟶ A₃₂} {g₂₃ : A₂₃ ⟶ A₃₃} {g₂₄ : A₂₄ ⟶ A₃₄} {g₂₅ : A₂₅ ⟶ A₃₅}
variables {f₃₁ : A₃₁ ⟶ A₃₂} {f₃₂ : A₃₂ ⟶ A₃₃} {f₃₃ : A₃₃ ⟶ A₃₄} {f₃₄ : A₃₄ ⟶ A₃₅}
variables {g₃₁ : A₃₁ ⟶ A₄₁} {g₃₂ : A₃₂ ⟶ A₄₂} {g₃₃ : A₃₃ ⟶ A₄₃} {g₃₄ : A₃₄ ⟶ A₄₄} {g₃₅ : A₃₅ ⟶ A₄₅}
variables {f₄₁ : A₄₁ ⟶ A₄₂} {f₄₂ : A₄₂ ⟶ A₄₃} {f₄₃ : A₄₃ ⟶ A₄₄} {f₄₄ : A₄₄ ⟶ A₄₅}
variables {g₄₁ : A₄₁ ⟶ A₅₁} {g₄₂ : A₄₂ ⟶ A₅₂} {g₄₃ : A₄₃ ⟶ A₅₃} {g₄₄ : A₄₄ ⟶ A₅₄} {g₄₅ : A₄₅ ⟶ A₅₅}
variables {f₅₁ : A₅₁ ⟶ A₅₂} {f₅₂ : A₅₂ ⟶ A₅₃} {f₅₃ : A₅₃ ⟶ A₅₄} {f₅₄ : A₅₄ ⟶ A₅₅}

namespace bicartesian

def quatro_cons (h : exact_seq 𝓐 [f₁₁, f₁₂, f₁₃, f₁₄]) : cochain_complex 𝓐 ℕ :=
((((((cochain_complex.cons homological_complex.zero (cokernel f₁₄) 0 zero_comp).cons
  _ (cokernel.π _) comp_zero).cons
  _ f₁₄ $ cokernel.condition _).cons
  _ f₁₃ $ (h.drop 2).pair.w).cons
  _ f₁₂ $ (h.drop 1).pair.w).cons
  _ f₁₁ $ (h.drop 0).pair.w).cons
  _ (kernel.ι _) $ kernel.condition _

open cochain_complex.hom (cons)

def quatro_cons_hom
  (h₁ : exact_seq 𝓐 [f₁₁, f₁₂, f₁₃, f₁₄])
  (h₂ : exact_seq 𝓐 [f₂₁, f₂₂, f₂₃, f₂₄])
  (sq₁ : commsq f₁₁ g₁₁ g₁₂ f₂₁)
  (sq₂ : commsq f₁₂ g₁₂ g₁₃ f₂₂)
  (sq₃ : commsq f₁₃ g₁₃ g₁₄ f₂₃)
  (sq₄ : commsq f₁₄ g₁₄ g₁₅ f₂₄) :
  quatro_cons h₁ ⟶ quatro_cons h₂ :=
cochain_complex.hom.cons _ _ (kernel.map _ _ _ _ sq₁.w)
  (cons _ _ g₁₁
  (cons _ _ g₁₂
  (cons _ _ g₁₃
  (cons _ _ g₁₄
  (cons _ _ g₁₅
  (cons _ _ (cokernel.map _ _ _ _ sq₄.w) 0 $
    comp_zero.trans comp_zero.symm) $
    (cokernel.π_desc _ _ _).symm) $
    sq₄.w.symm) sq₃.w.symm) sq₂.w.symm) sq₁.w.symm) $
    kernel.lift_ι _ _ _

variables
  (h₁ : exact_seq 𝓐 [f₁₁, f₁₂, f₁₃, f₁₄])
  (h₂ : exact_seq 𝓐 [f₂₁, f₂₂, f₂₃, f₂₄])
  (sq₁ : commsq f₁₁ g₁₁ g₁₂ f₂₁)
  (sq₂ : commsq f₁₂ g₁₂ g₁₃ f₂₂)
  (sq₃ : commsq f₁₃ g₁₃ g₁₄ f₂₃)
  (sq₄ : commsq f₁₄ g₁₄ g₁₅ f₂₄)

def quatro_cone : cochain_complex 𝓐 ℤ :=
homological_complex.cone $
  (homological_complex.embed complex_shape.embedding.nat_up_int_up).map $
  quatro_cons_hom h₁ h₂ sq₁ sq₂ sq₃ sq₄

@[simp] lemma quatro_cone_X_1 :
  (quatro_cone h₁ h₂ sq₁ sq₂ sq₃ sq₄).X 1 = (A₁₂ ⊞ A₂₁) := rfl

@[simp] lemma quatro_cone_X_2 :
  (quatro_cone h₁ h₂ sq₁ sq₂ sq₃ sq₄).X 2 = (A₁₃ ⊞ A₂₂) := rfl

@[simp] lemma quatro_cone_X_3 :
  (quatro_cone h₁ h₂ sq₁ sq₂ sq₃ sq₄).X 3 = (A₁₄ ⊞ A₂₃) := rfl

-- move me
def biprod.matrix
  (f₁₁ : A₁₁ ⟶ A₂₁) (f₂₁ : A₁₂ ⟶ A₂₁) (f₁₂ : A₁₁ ⟶ A₂₂) (f₂₂ : A₁₂ ⟶ A₂₂) :
  A₁₁ ⊞ A₁₂ ⟶ A₂₁ ⊞ A₂₂ :=
biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂)

@[simp] lemma quatro_cone_d_12' :
  (quatro_cone h₁ h₂ sq₁ sq₂ sq₃ sq₄).d 1 2 =
  biprod.matrix (-f₁₂) 0 (g₁₂ ≫ 𝟙 _) f₂₁ :=
rfl

@[simp] lemma quatro_cone_d_23' :
  (quatro_cone h₁ h₂ sq₁ sq₂ sq₃ sq₄).d 2 3 =
  biprod.matrix (-f₁₃) 0 (g₁₃ ≫ 𝟙 _) f₂₂ :=
rfl

@[simp] lemma quatro_cone_d_34' :
  (quatro_cone h₁ h₂ sq₁ sq₂ sq₃ sq₄).d 3 4 =
  biprod.matrix (-f₁₄) 0 (g₁₄ ≫ 𝟙 _) f₂₃ :=
rfl

section homotopy_category
open homotopy_category

instance quatro_cons_acyclic :
  is_acyclic ((homotopy_category.quotient _ _).obj $
  (homological_complex.embed complex_shape.embedding.nat_up_int_up).obj
  (quatro_cons h₁)) :=
begin
  constructor,
  intro n,
  obtain ⟨n, rfl⟩ : ∃ k, k+1 = n := ⟨n-1, sub_add_cancel _ _⟩,
  refine is_zero.of_iso _ (homology_iso _ n (n+1) (n+1+1) rfl rfl),
  refine exact.homology_is_zero _ _ _,
  rcases n with ((_|_|_|_|_|_|n)|(_|n)),
  { exact exact_kernel_ι },
  { exact (h₁.drop 0).pair },
  { exact (h₁.drop 1).pair },
  { exact (h₁.drop 2).pair },
  { exact abelian.exact_cokernel _ },
  { show exact (cokernel.π _) _, exact exact_epi_zero _, },
  { exact exact_of_zero _ _ },
  { show exact _ (kernel.ι _), exact exact_zero_mono _ },
  { exact exact_of_zero _ _ },
end

lemma quatro_cons_hom_quasi_iso :
  is_quasi_iso $
    (homotopy_category.quotient _ _).map $
    (homological_complex.embed complex_shape.embedding.nat_up_int_up).map $
    (quatro_cons_hom h₁ h₂ sq₁ sq₂ sq₃ sq₄) :=
begin
  constructor,
  intro n,
  refine is_zero.is_iso _ _ _;
  apply is_acyclic.cond,
end

end homotopy_category

-- #check biprod.matrix (-f₁₂) 0 (g₁₂ ≫ 𝟙 _) f₂₁

end bicartesian
