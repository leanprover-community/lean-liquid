import category_theory.abelian.homology

import for_mathlib.exact_seq3
import for_mathlib.homology_exact
.

noncomputable theory

open category_theory category_theory.limits

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

structure sum_str (A B X : 𝓐) :=
(inl : A ⟶ X)
(inr : B ⟶ X)
(fst : X ⟶ A)
(snd : X ⟶ B)
(inl_fst : inl ≫ fst = 𝟙 _)
(inr_snd : inr ≫ snd = 𝟙 _)
(inl_snd : inl ≫ snd = 0)
(inr_fst : inr ≫ fst = 0)
(total : fst ≫ inl + snd ≫ inr = 𝟙 _)

namespace sum_str

variables {A B X : 𝓐}

attribute [reassoc] sum_str.inl_fst sum_str.inr_snd sum_str.inl_snd sum_str.inr_fst

@[simps]
def biprod (A B : 𝓐) : sum_str A B (A ⊞ B) :=
{ inl := biprod.inl,
  inr := biprod.inr,
  fst := biprod.fst,
  snd := biprod.snd,
  inl_fst := biprod.inl_fst,
  inr_snd := biprod.inr_snd,
  inl_snd := biprod.inl_snd,
  inr_fst := biprod.inr_fst,
  total := biprod.total }

@[simps]
def symm (sum : sum_str A B X) : sum_str B A X :=
{ inl := sum.inr,
  inr := sum.inl,
  fst := sum.snd,
  snd := sum.fst,
  inl_fst := sum.inr_snd,
  inr_snd := sum.inl_fst,
  inl_snd := sum.inr_fst,
  inr_fst := sum.inl_snd,
  total := by { rw [add_comm, sum.total], } }

open opposite

@[simps]
protected def op (sum : sum_str A B X) : sum_str (op A) (op B) (op X) :=
{ inl := sum.fst.op,
  inr := sum.snd.op,
  fst := sum.inl.op,
  snd := sum.inr.op,
  inl_fst := by { rw [← op_comp, sum.inl_fst, op_id] },
  inr_snd := by { rw [← op_comp, sum.inr_snd, op_id] },
  inl_snd := by { rw [← op_comp, sum.inr_fst, op_zero] },
  inr_fst := by { rw [← op_comp, sum.inl_snd, op_zero] },
  total := by { rw [← op_comp, ← op_comp, ← op_add, sum.total, op_id] } }

@[simps]
protected def unop {A B X : 𝓐ᵒᵖ} (sum : sum_str A B X) : sum_str (unop A) (unop B) (unop X) :=
{ inl := sum.fst.unop,
  inr := sum.snd.unop,
  fst := sum.inl.unop,
  snd := sum.inr.unop,
  inl_fst := by { rw [← unop_comp, sum.inl_fst, unop_id] },
  inr_snd := by { rw [← unop_comp, sum.inr_snd, unop_id] },
  inl_snd := by { rw [← unop_comp, sum.inr_fst, unop_zero] },
  inr_fst := by { rw [← unop_comp, sum.inl_snd, unop_zero] },
  total := by { rw [← unop_comp, ← unop_comp, ← unop_add, sum.total, unop_id] } }

lemma symm_symm (sum : sum_str A B X) : sum.symm.symm = sum :=
by { cases sum, refl }

lemma op_symm (sum : sum_str A B X) : sum.symm.op = sum.op.symm :=
by { cases sum, refl }

lemma unop_symm {A B X : 𝓐ᵒᵖ} (sum : sum_str A B X) : sum.symm.unop = sum.unop.symm :=
by { cases sum, refl }

lemma unop_op (sum : sum_str A B X) : sum.op.unop = sum :=
by { cases sum, refl }

lemma op_unop {A B X : 𝓐ᵒᵖ} (sum : sum_str A B X) : sum.unop.op = sum :=
by { cases sum, refl }

end sum_str

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

section

variables (f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)

/-- A *local bicomplex* is a commutative diagram of the following shape
```
A₁₁ --- f₁₁ --> A₁₂
 |               |
g₁₁             g₁₂
 |               |
 v               v
A₂₁ --- f₂₁ --> A₂₂ --- f₂₂ --> A₂₃
                 |               |
                g₂₂             g₂₃
                 |               |
                 v               v
                A₃₂ --- f₃₂ --> A₃₃

```
whose rows and columns are complexes. -/
@[ext] structure LBC :=
(hw : f₂₁ ≫ f₂₂ = 0)
(vw : g₁₂ ≫ g₂₂ = 0)
(diag_in : A₁₁ ⟶ A₂₂)
(diag_out : A₂₂ ⟶ A₃₃)
(diag_in_tr₁ : g₁₁ ≫ f₂₁ = diag_in)
(diag_in_tr₂ : f₁₁ ≫ g₁₂ = diag_in)
(diag_out_tr₁ : g₂₂ ≫ f₃₂ = diag_out)
(diag_out_tr₂ : f₂₂ ≫ g₂₃ = diag_out)
(X Y : 𝓐)
(sum₁ : sum_str A₁₂ A₂₁ X)
(sum₂ : sum_str A₂₃ A₃₂ Y)
(π : X ⟶ A₂₂)
(ι : A₂₂ ⟶ Y)
(inl_π : sum₁.inl ≫ π = g₁₂)
(inr_π : sum₁.inr ≫ π = f₂₁)
(ι_fst : ι ≫ sum₂.fst = f₂₂)
(ι_snd : ι ≫ sum₂.snd = g₂₂)

structure LBC.core :=
(hw : f₂₁ ≫ f₂₂ = 0)
(vw : g₁₂ ≫ g₂₂ = 0)
(sq₁ : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁)
(sq₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂)

end

namespace LBC

attribute [reassoc] LBC.hw LBC.vw

@[reassoc] lemma sq₁ (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁ :=
by rw [lbc.diag_in_tr₁, diag_in_tr₂]

@[reassoc] lemma sq₂ (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂ :=
by rw [lbc.diag_out_tr₁, diag_out_tr₂]

@[simps]
def of_core (lbc : core f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂ :=
{ hw := lbc.hw,
  vw := lbc.vw,
  diag_in := g₁₁ ≫ f₂₁,
  diag_out := g₂₂ ≫ f₃₂,
  diag_in_tr₁ := rfl,
  diag_in_tr₂ := lbc.sq₁,
  diag_out_tr₁ := rfl,
  diag_out_tr₂ := lbc.sq₂,
  X := A₁₂ ⊞ A₂₁,
  Y := A₂₃ ⊞ A₃₂,
  sum₁ := sum_str.biprod _ _,
  sum₂ := sum_str.biprod _ _,
  π := biprod.desc g₁₂ f₂₁,
  ι := biprod.lift f₂₂ g₂₂,
  inl_π := biprod.inl_desc _ _,
  inr_π := biprod.inr_desc _ _,
  ι_fst := biprod.lift_fst _ _,
  ι_snd := biprod.lift_snd _ _, }

@[simps]
def symm (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  LBC g₁₁ f₁₁ f₂₁ g₁₂ g₂₂ f₂₂ f₃₂ g₂₃ :=
{ hw := lbc.vw,
  vw := lbc.hw,
  diag_in := lbc.diag_in,
  diag_out := lbc.diag_out,
  diag_in_tr₁ := lbc.diag_in_tr₂,
  diag_in_tr₂ := lbc.diag_in_tr₁,
  diag_out_tr₁ := lbc.diag_out_tr₂,
  diag_out_tr₂ := lbc.diag_out_tr₁,
  X := lbc.X,
  Y := lbc.Y,
  sum₁ := lbc.sum₁.symm,
  sum₂ := lbc.sum₂.symm,
  π := lbc.π,
  ι := lbc.ι,
  inl_π := lbc.inr_π,
  inr_π := lbc.inl_π,
  ι_fst := lbc.ι_snd,
  ι_snd := lbc.ι_fst }

section
open opposite

@[simps]
protected def op (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  LBC f₃₂.op g₂₃.op g₂₂.op f₂₂.op f₂₁.op g₁₂.op g₁₁.op f₁₁.op :=
{ hw := by { rw [← op_comp, lbc.hw, op_zero] },
  vw := by { rw [← op_comp, lbc.vw, op_zero] },
  diag_in := lbc.diag_out.op,
  diag_out := lbc.diag_in.op,
  diag_in_tr₁ := by { rw [← op_comp, lbc.diag_out_tr₂] },
  diag_in_tr₂ := by { rw [← op_comp, lbc.diag_out_tr₁] },
  diag_out_tr₁ := by { rw [← op_comp, lbc.diag_in_tr₂] },
  diag_out_tr₂ := by { rw [← op_comp, lbc.diag_in_tr₁] },
  X := op lbc.Y,
  Y := op lbc.X,
  sum₁ := lbc.symm.sum₂.op,
  sum₂ := lbc.symm.sum₁.op,
  π := lbc.ι.op,
  ι := lbc.π.op,
  inl_π := by { dsimp, rw [← op_comp, lbc.ι_snd], },
  inr_π := by { dsimp, rw [← op_comp, lbc.ι_fst], },
  ι_fst := by { dsimp, rw [← op_comp, lbc.inr_π], },
  ι_snd := by { dsimp, rw [← op_comp, lbc.inl_π], } }

variables {A'₁₁ A'₁₂ A'₁₃ A'₁₄ A'₁₅ : 𝓐ᵒᵖ}
variables {A'₂₁ A'₂₂ A'₂₃ A'₂₄ A'₂₅ : 𝓐ᵒᵖ}
variables {A'₃₁ A'₃₂ A'₃₃ A'₃₄ A'₃₅ : 𝓐ᵒᵖ}
variables {A'₄₁ A'₄₂ A'₄₃ A'₄₄ A'₄₅ : 𝓐ᵒᵖ}
variables {A'₅₁ A'₅₂ A'₅₃ A'₅₄ A'₅₅ : 𝓐ᵒᵖ}

variables {f'₁₁ : A'₁₁ ⟶ A'₁₂} {f'₁₂ : A'₁₂ ⟶ A'₁₃} {f'₁₃ : A'₁₃ ⟶ A'₁₄} {f'₁₄ : A'₁₄ ⟶ A'₁₅}
variables {g'₁₁ : A'₁₁ ⟶ A'₂₁} {g'₁₂ : A'₁₂ ⟶ A'₂₂} {g'₁₃ : A'₁₃ ⟶ A'₂₃} {g'₁₄ : A'₁₄ ⟶ A'₂₄} {g'₁₅ : A'₁₅ ⟶ A'₂₅}
variables {f'₂₁ : A'₂₁ ⟶ A'₂₂} {f'₂₂ : A'₂₂ ⟶ A'₂₃} {f'₂₃ : A'₂₃ ⟶ A'₂₄} {f'₂₄ : A'₂₄ ⟶ A'₂₅}
variables {g'₂₁ : A'₂₁ ⟶ A'₃₁} {g'₂₂ : A'₂₂ ⟶ A'₃₂} {g'₂₃ : A'₂₃ ⟶ A'₃₃} {g'₂₄ : A'₂₄ ⟶ A'₃₄} {g'₂₅ : A'₂₅ ⟶ A'₃₅}
variables {f'₃₁ : A'₃₁ ⟶ A'₃₂} {f'₃₂ : A'₃₂ ⟶ A'₃₃} {f'₃₃ : A'₃₃ ⟶ A'₃₄} {f'₃₄ : A'₃₄ ⟶ A'₃₅}
variables {g'₃₁ : A'₃₁ ⟶ A'₄₁} {g'₃₂ : A'₃₂ ⟶ A'₄₂} {g'₃₃ : A'₃₃ ⟶ A'₄₃} {g'₃₄ : A'₃₄ ⟶ A'₄₄} {g'₃₅ : A'₃₅ ⟶ A'₄₅}
variables {f'₄₁ : A'₄₁ ⟶ A'₄₂} {f'₄₂ : A'₄₂ ⟶ A'₄₃} {f'₄₃ : A'₄₃ ⟶ A'₄₄} {f'₄₄ : A'₄₄ ⟶ A'₄₅}
variables {g'₄₁ : A'₄₁ ⟶ A'₅₁} {g'₄₂ : A'₄₂ ⟶ A'₅₂} {g'₄₃ : A'₄₃ ⟶ A'₅₃} {g'₄₄ : A'₄₄ ⟶ A'₅₄} {g'₄₅ : A'₄₅ ⟶ A'₅₅}
variables {f'₅₁ : A'₅₁ ⟶ A'₅₂} {f'₅₂ : A'₅₂ ⟶ A'₅₃} {f'₅₃ : A'₅₃ ⟶ A'₅₄} {f'₅₄ : A'₅₄ ⟶ A'₅₅}

@[simps]
protected def unop (lbc : LBC f'₁₁ g'₁₁ g'₁₂ f'₂₁ f'₂₂ g'₂₂ g'₂₃ f'₃₂) :
  LBC f'₃₂.unop g'₂₃.unop g'₂₂.unop f'₂₂.unop f'₂₁.unop g'₁₂.unop g'₁₁.unop f'₁₁.unop :=
{ hw := by { rw [← unop_comp, lbc.hw, unop_zero] },
  vw := by { rw [← unop_comp, lbc.vw, unop_zero] },
  diag_in := lbc.diag_out.unop,
  diag_out := lbc.diag_in.unop,
  diag_in_tr₁ := by { rw [← unop_comp, lbc.diag_out_tr₂] },
  diag_in_tr₂ := by { rw [← unop_comp, lbc.diag_out_tr₁] },
  diag_out_tr₁ := by { rw [← unop_comp, lbc.diag_in_tr₂] },
  diag_out_tr₂ := by { rw [← unop_comp, lbc.diag_in_tr₁] },
  X := unop lbc.Y,
  Y := unop lbc.X,
  sum₁ := lbc.symm.sum₂.unop,
  sum₂ := lbc.symm.sum₁.unop,
  π := lbc.ι.unop,
  ι := lbc.π.unop,
  inl_π := by { dsimp, rw [← unop_comp, lbc.ι_snd], },
  inr_π := by { dsimp, rw [← unop_comp, lbc.ι_fst], },
  ι_fst := by { dsimp, rw [← unop_comp, lbc.inr_π], },
  ι_snd := by { dsimp, rw [← unop_comp, lbc.inl_π], } }
.

lemma unop_op (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) : lbc.op.unop = lbc :=
begin
  cases lbc, ext; try { refl },
  { dsimp, rw [← sum_str.op_symm, sum_str.unop_op, sum_str.symm_symm], },
  { dsimp, rw [← sum_str.op_symm, sum_str.unop_op, sum_str.symm_symm], },
end

lemma op_unop (lbc : LBC f'₁₁ g'₁₁ g'₁₂ f'₂₁ f'₂₂ g'₂₂ g'₂₃ f'₃₂) : lbc.unop.op = lbc :=
begin
  cases lbc, ext; try { refl },
  { dsimp, rw [← sum_str.unop_symm, sum_str.op_unop, sum_str.symm_symm], },
  { dsimp, rw [← sum_str.unop_symm, sum_str.op_unop, sum_str.symm_symm], },
end

end

@[reassoc] lemma diag_in_r (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  lbc.diag_in ≫ f₂₂ = 0 :=
by rw [← lbc.diag_in_tr₁, category.assoc, lbc.hw, comp_zero]

@[reassoc] lemma diag_in_d (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  lbc.diag_in ≫ g₂₂ = 0 :=
by rw [← lbc.diag_in_tr₂, category.assoc, lbc.vw, comp_zero]

@[reassoc] lemma r_diag_out (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  f₂₁ ≫ lbc.diag_out = 0 :=
by rw [← lbc.diag_out_tr₂, ← category.assoc, lbc.hw, zero_comp]

@[reassoc] lemma d_diag_out (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  g₁₂ ≫ lbc.diag_out = 0 :=
by rw [← lbc.diag_out_tr₁, ← category.assoc, lbc.vw, zero_comp]

lemma π_eq (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  lbc.π = lbc.sum₁.fst ≫ g₁₂ + lbc.sum₁.snd ≫ f₂₁ :=
by rw [← category.id_comp lbc.π, ← lbc.sum₁.total, preadditive.add_comp,
  category.assoc, category.assoc, lbc.inl_π, lbc.inr_π]

lemma ι_eq (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  lbc.ι = f₂₂ ≫ lbc.sum₂.inl + g₂₂ ≫ lbc.sum₂.inr :=
by rw [← category.comp_id lbc.ι, ← lbc.sum₂.total, preadditive.comp_add,
  ← category.assoc, ← category.assoc, lbc.ι_fst, lbc.ι_snd]

lemma diag_in_ι (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  lbc.diag_in ≫ lbc.ι = 0 :=
by simp only [lbc.ι_eq, preadditive.comp_add, category.assoc, zero_comp, add_zero,
    reassoc_of lbc.ι_fst, reassoc_of lbc.ι_snd, lbc.diag_in_r_assoc, lbc.diag_in_d_assoc]

lemma π_diag_out (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  lbc.π ≫ lbc.diag_out = 0 :=
by simp only [lbc.π_eq, preadditive.add_comp, category.assoc, comp_zero, add_zero,
    reassoc_of lbc.inl_π, reassoc_of lbc.inr_π, lbc.r_diag_out, lbc.d_diag_out]

lemma drd₁ (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  g₁₁ ≫ f₂₁ ≫ g₂₂ = 0 :=
by rw [← lbc.sq₁_assoc, lbc.vw, comp_zero]

lemma drd₂ (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  g₁₂ ≫ f₂₂ ≫ g₂₃ = 0 :=
by rw [lbc.sq₂, lbc.vw_assoc, zero_comp]

lemma rdr₁ (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  f₁₁ ≫ g₁₂ ≫ f₂₂ = 0 :=
by rw [lbc.sq₁_assoc, lbc.hw, comp_zero]

lemma rdr₂ (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) :
  f₂₁ ≫ g₂₂ ≫ f₃₂ = 0 :=
by rw [← lbc.sq₂, lbc.hw_assoc, zero_comp]

/-- The *receptor* of a local bicomplex. -/
def rcp (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) : 𝓐 :=
homology lbc.diag_in lbc.ι lbc.diag_in_ι

/-- The *donor* of a local bicomplex. -/
def don (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) : 𝓐 :=
homology lbc.π lbc.diag_out lbc.π_diag_out

/-- The *horizontal homology* of a local bicomplex. -/
def H (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) : 𝓐 :=
homology f₂₁ f₂₂ lbc.hw

/-- The *vertical homology* of a local bicomplex. -/
def V (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂) : 𝓐 :=
homology g₁₂ g₂₂ lbc.vw

variables (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)

lemma H_is_zero_iff : is_zero lbc.H ↔ exact f₂₁ f₂₂ :=
begin
  rw preadditive.exact_iff_homology_zero,
  simp only [lbc.hw, eq_self_iff_true, exists_true_left],
  split,
  refine λ h, ⟨h.iso_zero⟩,
  rintro ⟨i⟩, exact is_zero_of_iso_of_zero (is_zero_zero _) i.symm
end

lemma V_is_zero_iff : is_zero lbc.V ↔ exact g₁₂ g₂₂ :=
lbc.symm.H_is_zero_iff

/-- The intramural map from the receptor to the horizontal homology. -/
def rcp_to_H : lbc.rcp ⟶ lbc.H :=
homology.map _ _
  { left := g₁₁,
    right := 𝟙 _,
    w' := by { dsimp, rw [category.comp_id, lbc.diag_in_tr₁], } }
  { left := 𝟙 _,
    right := lbc.sum₂.fst,
    w' := by { dsimp, rw [category.id_comp, lbc.ι_fst], } }
  rfl

/-- The intramural map from the receptor to the vertical homology. -/
def rcp_to_V : lbc.rcp ⟶ lbc.V :=
homology.map _ _
  { left := f₁₁,
    right := 𝟙 _,
    w' := by { dsimp, rw [category.comp_id, lbc.diag_in_tr₂], } }
  { left := 𝟙 _,
    right := lbc.sum₂.snd,
    w' := by { dsimp, rw [category.id_comp, lbc.ι_snd], } }
  rfl

/-- The intramural map from the horizontal homology to the donor. -/
def H_to_don : lbc.H ⟶ lbc.don :=
homology.map _ _
  { left := lbc.sum₁.inr,
    right := 𝟙 _,
    w' := by { dsimp, rw [category.comp_id, lbc.inr_π], } }
  { left := 𝟙 _,
    right := g₂₃,
    w' := by { dsimp, rw [category.id_comp, lbc.diag_out_tr₂], } }
  rfl

/-- The intramural map from the vertical homology to the donor. -/
def V_to_don : lbc.V ⟶ lbc.don :=
homology.map _ _
  { left := lbc.sum₁.inl,
    right := 𝟙 _,
    w' := by { dsimp, rw [category.comp_id, lbc.inl_π], } }
  { left := 𝟙 _,
    right := f₃₂,
    w' := by { dsimp, rw [category.id_comp, lbc.diag_out_tr₁], } }
  rfl

lemma rcp_to_H_comp_H_to_don : lbc.rcp_to_H ≫ lbc.H_to_don = lbc.rcp_to_V ≫ lbc.V_to_don :=
begin
  delta rcp_to_H H_to_don rcp_to_V V_to_don,
  rw [homology.map_comp, homology.map_comp],
  refl,
end

/-- The horizontal extramural map. -/
def ex_h
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₁₂ g₁₂ g₁₃ f₂₂ f₂₃ g₂₃ g₂₄ f₃₃) :
  lbc₁.don ⟶ lbc₂.rcp :=
homology.map _ _
  { left := lbc₁.sum₁.fst,
    right := f₂₂,
    w' := by { dsimp, rw [lbc₁.π_eq, preadditive.add_comp, category.assoc, category.assoc,
      lbc₁.hw, comp_zero, add_zero, lbc₂.diag_in_tr₁], } }
  { left := f₂₂,
    right := lbc₂.sum₂.inr,
    w' := by { dsimp, rw [lbc₂.ι_eq, preadditive.comp_add, ← category.assoc, ← category.assoc,
      lbc₂.hw, zero_comp, zero_add, lbc₁.diag_out_tr₂], } }
  rfl
.

lemma V_to_don_comp_ex_h_comp_rcp_to_V
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₁₂ g₁₂ g₁₃ f₂₂ f₂₃ g₂₃ g₂₄ f₃₃) :
  lbc₁.V_to_don ≫ ex_h lbc₁ lbc₂ ≫ lbc₂.rcp_to_V =
  homology.map _ _ ⟨f₁₂, f₂₂, lbc₂.sq₁⟩ ⟨f₂₂, f₃₂, lbc₁.sq₂⟩ rfl :=
begin
  delta V_to_don ex_h rcp_to_V,
  rw [homology.map_comp, homology.map_comp],
  congr' 1; apply category_theory.comma_morphism.ext; dsimp;
  simp only [sum_str.inl_fst, sum_str.inl_fst_assoc, sum_str.inr_snd, sum_str.inr_snd_assoc,
    category.id_comp, category.comp_id],
end

/-- The vertical extramural map. -/
def ex_v
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₂₁ g₂₁ g₂₂ f₃₁ f₃₂ g₃₂ g₃₃ f₄₂) :
  lbc₁.don ⟶ lbc₂.rcp :=
homology.map _ _
  { left := lbc₁.sum₁.snd,
    right := g₂₂,
    w' := by { dsimp, rw [lbc₁.π_eq, preadditive.add_comp, category.assoc, category.assoc,
      lbc₁.vw, comp_zero, zero_add, lbc₂.diag_in_tr₂], } }
  { left := g₂₂,
    right := lbc₂.sum₂.inl,
    w' := by { dsimp, rw [lbc₂.ι_eq, preadditive.comp_add, ← category.assoc, ← category.assoc,
      lbc₂.vw, zero_comp, add_zero, lbc₁.diag_out_tr₁], } }
  rfl
.

lemma H_to_don_comp_ex_v_comp_rcp_to_H
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₂₁ g₂₁ g₂₂ f₃₁ f₃₂ g₃₂ g₃₃ f₄₂) :
  lbc₁.H_to_don ≫ ex_v lbc₁ lbc₂ ≫ lbc₂.rcp_to_H =
  homology.map _ _ ⟨g₂₁, g₂₂, lbc₂.sq₁.symm⟩ ⟨g₂₂, g₂₃, lbc₁.sq₂.symm⟩ rfl :=
begin
  delta H_to_don ex_v rcp_to_H,
  rw [homology.map_comp, homology.map_comp],
  congr' 1; apply category_theory.comma_morphism.ext; dsimp;
  simp only [sum_str.inl_fst, sum_str.inl_fst_assoc, sum_str.inr_snd, sum_str.inr_snd_assoc,
    category.id_comp, category.comp_id],
end
.

open_locale pseudoelement
open category_theory.abelian

section

variables {A'₁₁ A'₁₂ A'₁₃ A'₁₄ A'₁₅ : 𝓐ᵒᵖ}
variables {A'₂₁ A'₂₂ A'₂₃ A'₂₄ A'₂₅ : 𝓐ᵒᵖ}
variables {A'₃₁ A'₃₂ A'₃₃ A'₃₄ A'₃₅ : 𝓐ᵒᵖ}
variables {A'₄₁ A'₄₂ A'₄₃ A'₄₄ A'₄₅ : 𝓐ᵒᵖ}
variables {A'₅₁ A'₅₂ A'₅₃ A'₅₄ A'₅₅ : 𝓐ᵒᵖ}

variables {f'₁₁ : A'₁₁ ⟶ A'₁₂} {f'₁₂ : A'₁₂ ⟶ A'₁₃} {f'₁₃ : A'₁₃ ⟶ A'₁₄} {f'₁₄ : A'₁₄ ⟶ A'₁₅}
variables {g'₁₁ : A'₁₁ ⟶ A'₂₁} {g'₁₂ : A'₁₂ ⟶ A'₂₂} {g'₁₃ : A'₁₃ ⟶ A'₂₃} {g'₁₄ : A'₁₄ ⟶ A'₂₄} {g'₁₅ : A'₁₅ ⟶ A'₂₅}
variables {f'₂₁ : A'₂₁ ⟶ A'₂₂} {f'₂₂ : A'₂₂ ⟶ A'₂₃} {f'₂₃ : A'₂₃ ⟶ A'₂₄} {f'₂₄ : A'₂₄ ⟶ A'₂₅}
variables {g'₂₁ : A'₂₁ ⟶ A'₃₁} {g'₂₂ : A'₂₂ ⟶ A'₃₂} {g'₂₃ : A'₂₃ ⟶ A'₃₃} {g'₂₄ : A'₂₄ ⟶ A'₃₄} {g'₂₅ : A'₂₅ ⟶ A'₃₅}
variables {f'₃₁ : A'₃₁ ⟶ A'₃₂} {f'₃₂ : A'₃₂ ⟶ A'₃₃} {f'₃₃ : A'₃₃ ⟶ A'₃₄} {f'₃₄ : A'₃₄ ⟶ A'₃₅}
variables {g'₃₁ : A'₃₁ ⟶ A'₄₁} {g'₃₂ : A'₃₂ ⟶ A'₄₂} {g'₃₃ : A'₃₃ ⟶ A'₄₃} {g'₃₄ : A'₃₄ ⟶ A'₄₄} {g'₃₅ : A'₃₅ ⟶ A'₄₅}
variables {f'₄₁ : A'₄₁ ⟶ A'₄₂} {f'₄₂ : A'₄₂ ⟶ A'₄₃} {f'₄₃ : A'₄₃ ⟶ A'₄₄} {f'₄₄ : A'₄₄ ⟶ A'₄₅}
variables {g'₄₁ : A'₄₁ ⟶ A'₅₁} {g'₄₂ : A'₄₂ ⟶ A'₅₂} {g'₄₃ : A'₄₃ ⟶ A'₅₃} {g'₄₄ : A'₄₄ ⟶ A'₅₄} {g'₄₅ : A'₄₅ ⟶ A'₅₅}
variables {f'₅₁ : A'₅₁ ⟶ A'₅₂} {f'₅₂ : A'₅₂ ⟶ A'₅₃} {f'₅₃ : A'₅₃ ⟶ A'₅₄} {f'₅₄ : A'₅₄ ⟶ A'₅₅}


open opposite

-- #check kernel_op_op
-- -- kernel f.op ≅ opposite.op (cokernel f)

-- #check kernel_op_unop
-- -- opposite.unop (kernel f.op) ≅ cokernel f

-- #check kernel_unop_op
-- -- opposite.op (kernel g.unop) ≅ cokernel g

-- #check kernel_unop_unop
-- -- kernel g.unop ≅ opposite.unop (cokernel g)

-- #check cokernel_op_op
-- -- cokernel f.op ≅ opposite.op (kernel f)

-- #check cokernel_op_unop
-- -- opposite.unop (cokernel f.op) ≅ kernel f

-- #check cokernel_unop_op
-- -- opposite.op (cokernel g.unop) ≅ kernel g

-- #check cokernel_unop_unop
-- -- cokernel g.unop ≅ opposite.unop (kernel g)

@[simps]
def homology_unop_iso {A B C : 𝓐ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  homology f g w ≅ op (homology g.unop f.unop (by { rw [← unop_comp, w, unop_zero] })) :=
homology_iso_cokernel_lift _ _ _ ≪≫
  cokernel.map_iso _ (cokernel.desc g.unop f.unop _).op (iso.refl _) (cokernel_unop_op _).symm
    (by { apply quiver.hom.unop_inj, ext,
      simp only [unop_comp, iso.symm_hom, cokernel_unop_op_inv, quiver.hom.unop_op,
        cokernel.π_desc_assoc, iso.refl_hom, category.id_comp, cokernel.π_desc],
      rw [← unop_comp, kernel.lift_ι] }) ≪≫
  cokernel_op_op _ ≪≫
  (homology_iso_kernel_desc _ _ _).op

def homology_op_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  homology g.op f.op (by rw [← op_comp, w, op_zero]) ≅ op (homology f g w) :=
homology_unop_iso _ _ _

attribute [reassoc] cokernel.map_desc

lemma op_H_to_don (lbc : LBC f'₁₁ g'₁₁ g'₁₂ f'₂₁ f'₂₂ g'₂₂ g'₂₃ f'₃₂) :
  lbc.H_to_don = (homology_unop_iso _ _ _).hom ≫ lbc.unop.rcp_to_H.op ≫
    (homology_unop_iso _ _ lbc.π_diag_out).inv :=
begin
  ext,
  simp only [category.assoc, H_to_don, rcp_to_H,
    homology_unop_iso_hom, homology_unop_iso_inv,
    unop_sum₂, symm_sum₁, sum_str.unop_fst, sum_str.symm_inl, homology.map_ι,
    homology.π'_ι_assoc, cokernel.π_desc,
    homology_iso_cokernel_lift, homology_iso_kernel_desc,
    homology_iso_cokernel_image_to_kernel',
    cokernel_epi_comp_hom, cokernel_epi_comp_inv,
    category_theory.limits.cokernel.map_desc_assoc,
    cokernel_iso_of_eq_hom_comp_desc_assoc,
    iso.trans_hom, iso.trans_inv, iso.symm_hom],
  sorry
end

lemma op_rcp_to_H (lbc : LBC f'₁₁ g'₁₁ g'₁₂ f'₂₁ f'₂₂ g'₂₂ g'₂₃ f'₃₂) :
  lbc.rcp_to_H = (homology_unop_iso _ _ lbc.diag_in_ι).hom ≫
    lbc.unop.H_to_don.op ≫ (homology_unop_iso _ _ _).inv :=
begin
  sorry
end

lemma op_V_to_don (lbc : LBC f'₁₁ g'₁₁ g'₁₂ f'₂₁ f'₂₂ g'₂₂ g'₂₃ f'₃₂) :
  lbc.V_to_don = (homology_unop_iso _ _ _).hom ≫ lbc.unop.rcp_to_V.op ≫
    (homology_unop_iso _ _ lbc.π_diag_out).inv :=
lbc.symm.op_H_to_don

lemma op_rcp_to_V (lbc : LBC f'₁₁ g'₁₁ g'₁₂ f'₂₁ f'₂₂ g'₂₂ g'₂₃ f'₃₂) :
  lbc.rcp_to_V = (homology_unop_iso _ _ lbc.diag_in_ι).hom ≫
    lbc.unop.V_to_don.op ≫ (homology_unop_iso _ _ _).inv :=
lbc.symm.op_rcp_to_H

lemma op_ex_h
  (lbc₁ : LBC f'₁₁ g'₁₁ g'₁₂ f'₂₁ f'₂₂ g'₂₂ g'₂₃ f'₃₂)
  (lbc₂ : LBC f'₁₂ g'₁₂ g'₁₃ f'₂₂ f'₂₃ g'₂₃ g'₂₄ f'₃₃) :
  lbc₁.ex_h lbc₂ = (homology_unop_iso _ _ lbc₁.π_diag_out).hom ≫
    (lbc₂.unop.ex_h lbc₁.unop).op ≫ (homology_unop_iso _ _ lbc₂.diag_in_ι).inv :=
sorry

lemma op_ex_v
  (lbc₁ : LBC f'₁₁ g'₁₁ g'₁₂ f'₂₁ f'₂₂ g'₂₂ g'₂₃ f'₃₂)
  (lbc₂ : LBC f'₂₁ g'₂₁ g'₂₂ f'₃₁ f'₃₂ g'₃₂ g'₃₃ f'₄₂) :
  lbc₁.ex_v lbc₂ = (homology_unop_iso _ _ lbc₁.π_diag_out).hom ≫
    (lbc₂.unop.ex_v lbc₁.unop).op ≫ (homology_unop_iso _ _ lbc₂.diag_in_ι).inv  :=
by convert lbc₁.symm.op_ex_h lbc₂.symm using 1

end

lemma exact_aux_1
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₂₁ g₂₁ g₂₂ f₃₁ f₃₂ g₃₂ g₃₃ f₄₂) :
  exact (lbc₁.ex_v lbc₂ ≫ lbc₂.rcp_to_H) lbc₂.H_to_don :=
begin
  -- apply pseudoelement.exact_of_pseudo_exact,
  -- split,
  -- { suffices : lbc₁.ex_v lbc₂ ≫ lbc₂.rcp_to_V = 0,
  --   { intro x,
  --     rw [← pseudoelement.comp_apply, category.assoc, rcp_to_H_comp_H_to_don,
  --       ← category.assoc, this, zero_comp, pseudoelement.zero_apply] },
  --   rw pseudoelement.eq_zero_iff,
  --   intro x,
  --   delta ex_v rcp_to_V,
  --  },

  -- refine preadditive.exact_of_iso_of_exact'
  --   (cokernel.desc _ _ _) _ _ _
  --   (homology_iso_cokernel_lift _ _ _).symm
  --   (homology_iso_cokernel_lift _ _ _).symm
  --   (homology_iso_cokernel_lift _ _ _).symm _ _ _,

  -- rw abelian.exact_iff, split,
  -- { suffices : lbc₁.ex_v lbc₂ ≫ lbc₂.rcp_to_V = 0,
  --   rw [category.assoc, rcp_to_H_comp_H_to_don, ← category.assoc, this, zero_comp],
  --   delta ex_v rcp_to_V,
  --   rw [homology.map_comp],
  --   apply homology.ext,
  --   rw [homology.π_map, comp_zero],
  --   dsimp [kernel_subobject_map, homology.π],
  --   simp only [category.comp_id],
  --   sorry },
  sorry
end

lemma exact_aux_2
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₁₂ g₁₂ g₁₃ f₂₂ f₂₃ g₂₃ g₂₄ f₃₃) :
  exact lbc₁.H_to_don (lbc₁.ex_h lbc₂) :=
begin
  sorry
end

lemma salamander_v
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₂₁ g₂₁ g₂₂ f₃₁ f₃₂ g₃₂ g₃₃ f₄₂)
  (lbc₃ : LBC f₂₂ g₂₂ g₂₃ f₃₂ f₃₃ g₃₃ g₃₄ f₄₃)
  (lbc₄ : LBC f₃₂ g₃₂ g₃₃ f₄₂ f₄₃ g₄₃ g₄₄ f₅₃) :
  exact_seq 𝓐 [
    lbc₁.ex_v lbc₂ ≫ lbc₂.rcp_to_H,
    lbc₂.H_to_don,
    lbc₂.ex_h lbc₃,
    lbc₃.rcp_to_H,
    lbc₃.H_to_don ≫ lbc₃.ex_v lbc₄] :=
begin
  refine (exact_aux_1 lbc₁ lbc₂).cons _,
  refine (exact_aux_2 lbc₂ lbc₃).cons _,
  have aux1 := (exact_aux_2 lbc₃.op lbc₂.op).unop,
  simp only [op_H_to_don, op_ex_h, unop_comp, ← iso.unop_hom, ← iso.unop_inv,
    exact_comp_iso, exact_iso_comp, exact_comp_hom_inv_comp_iff, quiver.hom.unop_op] at aux1,
  refine aux1.cons _,
  have aux2 := (exact_aux_1 lbc₄.op lbc₃.op).unop,
  simp only [op_H_to_don, op_ex_v, op_rcp_to_H, category.assoc, iso.inv_hom_id_assoc,
    unop_comp, ← iso.unop_hom, ← iso.unop_inv, quiver.hom.unop_op,
    exact_iso_comp, exact_comp_hom_inv_comp_iff] at aux2,
  simp only [← category.assoc, exact_comp_iso] at aux2,
  exact aux2.exact_seq,
end

lemma salamander_h
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₁₂ g₁₂ g₁₃ f₂₂ f₂₃ g₂₃ g₂₄ f₃₃)
  (lbc₃ : LBC f₂₂ g₂₂ g₂₃ f₃₂ f₃₃ g₃₃ g₃₄ f₄₃)
  (lbc₄ : LBC f₂₃ g₂₃ g₂₄ f₃₃ f₃₄ g₃₄ g₃₅ f₄₄) :
  exact_seq 𝓐 [
    lbc₁.ex_h lbc₂ ≫ lbc₂.rcp_to_V,
    lbc₂.V_to_don,
    lbc₂.ex_v lbc₃,
    lbc₃.rcp_to_V,
    lbc₃.V_to_don ≫ lbc₃.ex_h lbc₄] :=
by convert salamander_v lbc₁.symm lbc₂.symm lbc₃.symm lbc₄.symm using 1

open_locale zero_object

section
/-!
## Extramural isomorphisms
-/

lemma iso_ex_h
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₁₂ g₁₂ g₁₃ f₂₂ f₂₃ g₂₃ g₂₄ f₃₃)
  (h₁ : f₁₁ ≫ f₁₂ = 0) (h₂ : f₃₂ ≫ f₃₃ = 0)
  (H₁ : is_zero lbc₁.H) (H₂ : is_zero lbc₂.H) :
  is_iso (lbc₁.ex_h lbc₂) :=
begin
  have := (salamander_v _ lbc₁ lbc₂ _).drop 1, any_goals { exact 0 },
  rotate,
  { exact LBC.of_core ⟨h₁, zero_comp, zero_comp.trans zero_comp.symm, lbc₂.sq₁⟩, },
  { exact LBC.of_core ⟨h₂, comp_zero, lbc₁.sq₂, comp_zero.trans comp_zero.symm⟩, },
  exact this.is_iso_of_zero_of_zero (H₁.eq_of_src _ _) (H₂.eq_of_tgt _ _),
end

lemma iso_ex_v
  (lbc₁ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (lbc₂ : LBC f₂₁ g₂₁ g₂₂ f₃₁ f₃₂ g₃₂ g₃₃ f₄₂)
  (h₁ : g₁₁ ≫ g₂₁ = 0) (h₂ : g₂₃ ≫ g₃₃ = 0)
  (H₁ : is_zero lbc₁.V) (H₂ : is_zero lbc₂.V) :
  is_iso (lbc₁.ex_v lbc₂) :=
by convert lbc₁.symm.iso_ex_h lbc₂.symm h₁ h₂ H₁ H₂ using 1

end

section intramural_isos

/-!
## Intramural isomorphisms

The subscripts at the end of the names indicate where the `0`s in the diagram are located:
`ₗ` = left, `ᵤ` = up, `ᵣ` = right, and `ₛ` down (south, thanks unicode).

-/

lemma iso_rcp_to_Hₗ
  (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (H₂₁ : is_zero A₂₁) (H₃₁ : is_zero A₃₁) (h : exact f₃₁ f₃₂) :
  is_iso lbc.rcp_to_H :=
begin
  have lbc₄ : LBC f₂₁ 0 g₂₂ f₃₁ f₃₂ 0 (0 : _ ⟶ 0) (0 : 0 ⟶ 0) :=
  LBC.of_core ⟨H₃₁.eq_of_src _ _, comp_zero, H₂₁.eq_of_src _ _, comp_zero.trans comp_zero.symm⟩,
  have lbc₃ : LBC 0 0 0 0 f₃₁ 0 0 0 :=
  LBC.of_core ⟨zero_comp, comp_zero, zero_comp.trans zero_comp.symm, comp_zero.trans comp_zero.symm⟩,
  haveI aux := iso_ex_h lbc₃ lbc₄ zero_comp zero_comp _ _, any_goals { exact 0 },
  rotate,
  { apply H₃₁.homology_is_zero, },
  { exact exact.homology_is_zero _ _ h, },
  have := (salamander_v _ _ lbc lbc₄).drop 2, any_goals { exact 0 },
  rotate,
  { exact LBC.of_core ⟨zero_comp, zero_comp, zero_comp.trans zero_comp.symm, lbc.sq₁⟩, },
  { exact LBC.of_core ⟨zero_comp, comp_zero, zero_comp.trans zero_comp.symm, H₂₁.eq_of_src _ _⟩, },
  refine this.is_iso_of_zero_of_zero _ _,
  { refine is_zero.eq_of_src _ _ _, apply H₂₁.homology_is_zero },
  { refine is_zero.eq_of_tgt _ _ _,
    apply is_zero_of_iso_of_zero _ (as_iso (lbc₃.ex_h lbc₄)),
    apply H₃₁.homology_is_zero, },
end

lemma iso_V_to_donₗ
  (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (H₂₁ : is_zero A₂₁) (H₃₁ : is_zero A₃₁) (h : exact f₃₁ f₃₂) :
  is_iso lbc.V_to_don :=
begin
  have lbc₄ : LBC f₂₁ 0 g₂₂ f₃₁ f₃₂ 0 (0 : _ ⟶ 0) (0 : 0 ⟶ 0) :=
  LBC.of_core ⟨H₃₁.eq_of_src _ _, comp_zero, H₂₁.eq_of_src _ _, comp_zero.trans comp_zero.symm⟩,
  have lbc₃ : LBC 0 0 0 0 f₃₁ 0 0 0 :=
  LBC.of_core ⟨zero_comp, comp_zero, zero_comp.trans zero_comp.symm, comp_zero.trans comp_zero.symm⟩,
  haveI aux := iso_ex_h lbc₃ lbc₄ zero_comp zero_comp _ _, any_goals { exact 0 },
  rotate,
  { apply H₃₁.homology_is_zero, },
  { exact exact.homology_is_zero _ _ h, },
  have := salamander_h _ lbc lbc₄ _, any_goals { exact 0 },
  rotate,
  { exact LBC.of_core ⟨zero_comp, comp_zero, zero_comp.trans zero_comp.symm, H₂₁.eq_of_src _ _⟩, },
  { exact LBC.of_core ⟨comp_zero, comp_zero, lbc.sq₂, comp_zero.trans comp_zero.symm⟩, },
  refine this.is_iso_of_zero_of_zero _ _,
  { refine is_zero.eq_of_src _ _ _, apply H₂₁.homology_is_zero },
  { refine is_zero.eq_of_tgt _ _ _,
    apply is_zero_of_iso_of_zero _ (as_iso (lbc₃.ex_h lbc₄)),
    apply H₃₁.homology_is_zero, },
end

lemma iso_rcp_to_Vᵤ
  (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (H₁₂ : is_zero A₁₂) (H₁₃ : is_zero A₁₃) (h : exact g₁₃ g₂₃) :
  is_iso lbc.rcp_to_V :=
lbc.symm.iso_rcp_to_Hₗ H₁₂ H₁₃ h

lemma iso_H_to_donᵤ
  (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (H₁₂ : is_zero A₁₂) (H₁₃ : is_zero A₁₃) (h : exact g₁₃ g₂₃) :
  is_iso lbc.H_to_don :=
lbc.symm.iso_V_to_donₗ H₁₂ H₁₃ h

lemma iso_H_to_donᵣ
  (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (H₁₂ : is_zero A₂₃) (H₁₃ : is_zero A₁₃) (h : exact f₁₁ f₁₂) :
  is_iso lbc.H_to_don :=
begin
  have aux := iso_rcp_to_Hₗ lbc.op H₁₂.op H₁₃.op h.op,
  simp only [op_rcp_to_H] at aux,
  replace aux := @is_iso.of_is_iso_comp_left _ _ _ _ _ _ _ _ aux,
  replace aux := @is_iso.of_is_iso_comp_right _ _ _ _ _ _ _ _ aux,
  rwa is_iso_op_iff at aux,
end

lemma iso_rcp_to_Vᵣ
  (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (H₁₂ : is_zero A₂₃) (H₁₃ : is_zero A₁₃) (h : exact f₁₁ f₁₂) :
  is_iso lbc.rcp_to_V :=
begin
  have aux := iso_V_to_donₗ lbc.op H₁₂.op H₁₃.op h.op,
  simp only [op_V_to_don] at aux,
  replace aux := @is_iso.of_is_iso_comp_left _ _ _ _ _ _ _ _ aux,
  replace aux := @is_iso.of_is_iso_comp_right _ _ _ _ _ _ _ _ aux,
  rwa is_iso_op_iff at aux,
end

lemma iso_rcp_to_Hₛ
  (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (H₃₁ : is_zero A₃₁) (H₃₂ : is_zero A₃₂) (h : exact g₁₁ g₂₁) :
  is_iso lbc.rcp_to_H :=
lbc.symm.iso_rcp_to_Vᵣ H₃₂ H₃₁ h


lemma iso_V_to_donₛ
  (lbc : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂)
  (H₃₁ : is_zero A₃₁) (H₃₂ : is_zero A₃₂) (h : exact g₁₁ g₂₁) :
  is_iso lbc.V_to_don :=
lbc.symm.iso_H_to_donᵣ H₃₂ H₃₁ h

end intramural_isos

section three_x_three

/-!
## The 3×3 lemma
-/

-- move me
theorem _root_.list.tfae.mp {l} (h : tfae l) (n₁ n₂) {a b}
  (h₁ : list.nth l n₁ = some a . tactic.interactive.refl)
  (h₂ : list.nth l n₂ = some b . tactic.interactive.refl) :
  a → b :=
(h.out n₁ n₂ h₁ h₂).mp

lemma three_x_three_top_row
  (Hr2 : exact f₂₁ f₂₂) (Hr3 : exact f₃₁ f₃₂)
  (Hc1 : exact g₁₁ g₂₁) (Hc2 : exact g₁₂ g₂₂) (Hc3 : exact g₁₃ g₂₃)
  (sq₁₁ : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁) (sq₁₂ : f₁₂ ≫ g₁₃ = g₁₂ ≫ f₂₂)
  (sq₂₁ : f₂₁ ≫ g₂₂ = g₂₁ ≫ f₃₁) (sq₂₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂)
  [mono f₂₁] [mono f₃₁] [mono g₁₁] [mono g₁₂] [mono g₁₃] :
  exact f₁₁ f₁₂ ∧ mono f₁₁ :=
begin
  have w : f₁₁ ≫ f₁₂ = 0,
  { rw [← cancel_mono g₁₃, zero_comp, category.assoc, sq₁₂, reassoc_of sq₁₁, Hr2.w, comp_zero], },
  let lbc₁₁ : LBC (0 : 0 ⟶ 0) (0 : 0 ⟶ 0) 0 0 f₁₁ g₁₁ g₁₂ f₂₁ :=
    LBC.of_core ⟨zero_comp, zero_comp, (is_zero_zero _).eq_of_src _ _, sq₁₁⟩,
  let lbc₁₂ : LBC (0 : 0 ⟶ 0) 0 0 f₁₁ f₁₂ g₁₂ g₁₃ f₂₂ :=
    LBC.of_core ⟨w, zero_comp, (is_zero_zero _).eq_of_src _ _, sq₁₂⟩,
  let lbc₂₁ : LBC 0 (0 : 0 ⟶ 0) g₁₁ 0 f₂₁ g₂₁ g₂₂ f₃₁ :=
    LBC.of_core ⟨zero_comp, Hc1.w, (is_zero_zero _).eq_of_src _ _, sq₂₁⟩,
  let lbc₂₂ : LBC f₁₁ g₁₁ g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂ :=
    LBC.of_core ⟨Hr2.w, Hc2.w, sq₁₁, sq₂₂⟩,
  suffices : is_zero lbc₁₁.H ∧ is_zero lbc₁₂.H,
  { refine ⟨exact_of_homology_is_zero this.2, _⟩,
    apply (tfae_mono (0:𝓐) f₁₁).mp 2 0,
    exact exact_of_homology_is_zero this.1, },
  split,
  { haveI e1 := lbc₁₁.iso_rcp_to_Hₗ (is_zero_zero _) (is_zero_zero _)
      ((tfae_mono (0:𝓐) f₂₁).mp 0 2 rfl rfl infer_instance),
    haveI e2 := lbc₁₁.iso_rcp_to_Vᵤ (is_zero_zero _) (is_zero_zero _)
      ((tfae_mono (0:𝓐) g₁₂).mp 0 2 rfl rfl infer_instance),
    refine is_zero_of_iso_of_zero _
      (as_iso $ inv lbc₁₁.rcp_to_V ≫ lbc₁₁.rcp_to_H),
    refine exact.homology_is_zero _ _ _,
    apply exact_zero_left_of_mono },
  { haveI e1 := lbc₁₂.iso_H_to_donᵤ (is_zero_zero _) (is_zero_zero _)
      ((tfae_mono (0:𝓐) g₁₃).mp 0 2 rfl rfl infer_instance),
    haveI e2 := lbc₁₂.iso_ex_v lbc₂₂ zero_comp Hc3.w
      (exact.homology_is_zero _ _ _) (Hc2.homology_is_zero _ _),
    swap, { apply exact_zero_left_of_mono },
    haveI e3 := lbc₂₁.iso_ex_h lbc₂₂ zero_comp Hr3.w
      (exact.homology_is_zero _ _ _) (Hr2.homology_is_zero _ _),
    swap, { apply exact_zero_left_of_mono },
    haveI e4 := lbc₂₁.iso_V_to_donₗ (is_zero_zero _) (is_zero_zero _)
      ((tfae_mono (0:𝓐) f₃₁).mp 0 2 rfl rfl infer_instance),
    have aux : is_zero lbc₂₁.V := Hc1.homology_is_zero _ _,
    apply is_zero_of_iso_of_zero aux,
    exact as_iso
      (lbc₂₁.V_to_don ≫ lbc₂₁.ex_h lbc₂₂ ≫ inv (lbc₁₂.ex_v lbc₂₂) ≫ inv lbc₁₂.H_to_don) }
end

lemma three_x_three_left_col
  (Hr1 : exact f₁₁ f₁₂) (Hr2 : exact f₂₁ f₂₂) (Hr3 : exact f₃₁ f₃₂)
  (Hc2 : exact g₁₂ g₂₂) (Hc3 : exact g₁₃ g₂₃)
  (sq₁₁ : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁) (sq₁₂ : f₁₂ ≫ g₁₃ = g₁₂ ≫ f₂₂)
  (sq₂₁ : f₂₁ ≫ g₂₂ = g₂₁ ≫ f₃₁) (sq₂₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂)
  [mono f₁₁] [mono f₂₁] [mono f₃₁] [mono g₁₂] [mono g₁₃] :
  exact g₁₁ g₂₁ ∧ mono g₁₁ :=
three_x_three_top_row Hc2 Hc3 Hr1 Hr2 Hr3 sq₁₁.symm sq₂₁.symm sq₁₂.symm sq₂₂.symm

lemma three_x_three_bot_row
  (Hr1 : exact f₁₁ f₁₂) (Hr2 : exact f₂₁ f₂₂)
  (Hc1 : exact g₁₁ g₂₁) (Hc2 : exact g₁₂ g₂₂) (Hc3 : exact g₁₃ g₂₃)
  (sq₁₁ : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁) (sq₁₂ : f₁₂ ≫ g₁₃ = g₁₂ ≫ f₂₂)
  (sq₂₁ : f₂₁ ≫ g₂₂ = g₂₁ ≫ f₃₁) (sq₂₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂)
  [epi f₁₂] [epi f₂₂] [epi g₂₁] [epi g₂₂] [epi g₂₃] :
  exact f₃₁ f₃₂ ∧ epi f₃₂ :=
begin
  have : exact f₃₂.op f₃₁.op ∧ mono f₃₂.op :=
    three_x_three_top_row Hr2.op Hr1.op Hc3.op Hc2.op Hc1.op _ _ _ _,
  { refine ⟨this.1.unop, _⟩, haveI := this.2, exact category_theory.unop_epi_of_mono f₃₂.op },
  all_goals { simp only [← op_comp, sq₁₁, sq₁₂, sq₂₁, sq₂₂] },
end

lemma three_x_three_right_col
  (Hr1 : exact f₁₁ f₁₂) (Hr2 : exact f₂₁ f₂₂) (Hr3 : exact f₃₁ f₃₂)
  (Hc1 : exact g₁₁ g₂₁) (Hc2 : exact g₁₂ g₂₂)
  (sq₁₁ : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁) (sq₁₂ : f₁₂ ≫ g₁₃ = g₁₂ ≫ f₂₂)
  (sq₂₁ : f₂₁ ≫ g₂₂ = g₂₁ ≫ f₃₁) (sq₂₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂)
  [epi f₁₂] [epi f₂₂] [epi f₃₂] [epi g₂₁] [epi g₂₂] :
  exact g₁₃ g₂₃ ∧ epi g₂₃ :=
three_x_three_bot_row Hc1 Hc2 Hr1 Hr2 Hr3 sq₁₁.symm sq₂₁.symm sq₁₂.symm sq₂₂.symm

end three_x_three

section four

/-!
## The four lemma

We prove a version of the four lemma that is slightly more general than the usual version.
-/

lemma four_lemma_top_epi
  (Hr1 : exact_seq 𝓐 [f₂₁, f₂₂, f₂₃]) (Hr2 : exact_seq 𝓐 [f₃₁, f₃₂, f₃₃])
  (Hc1 : exact g₁₂ g₂₂) (Hc2 : exact g₁₃ g₂₃)
  (sq₁₂ : f₁₂ ≫ g₁₃ = g₁₂ ≫ f₂₂)
  (sq₂₁ : f₂₁ ≫ g₂₂ = g₂₁ ≫ f₃₁) (sq₂₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂)
  (sq₂₃ : f₂₃ ≫ g₂₄ = g₂₃ ≫ f₃₃)
  [mono g₁₃] [epi g₂₁] [mono g₂₄] :
  epi f₁₂ :=
begin
  rw epi_iff_exact_zero_right,
  let lbc₁₃ : LBC (0 : 0 ⟶ 0) 0 0 f₁₂ (0 : _ ⟶ 0) g₁₃ 0 f₂₃ :=
    LBC.of_core ⟨comp_zero, zero_comp, (is_zero_zero _).eq_of_src _ _, _⟩,
  swap, { simp only [← cancel_mono g₂₄, zero_comp, category.assoc, sq₂₃, reassoc_of Hc2.w], },
  let lbc₂₂ : LBC (0 : 0 ⟶ _) 0 g₁₂ f₂₁ f₂₂ g₂₂ g₂₃ f₃₂ :=
    LBC.of_core ⟨Hr1.pair.w, Hc1.w, (is_zero_zero _).eq_of_src _ _, sq₂₂⟩,
  let lbc₂₃ : LBC f₁₂ g₁₂ g₁₃ f₂₂ f₂₃ g₂₃ g₂₄ f₃₃ :=
    LBC.of_core ⟨(Hr1.drop 1).pair.w, Hc2.w, sq₁₂, sq₂₃⟩,
  let lbc₃₁ : LBC 0 (0 : 0 ⟶ _) g₂₁ (kernel.ι f₃₁) f₃₁ 0 (cokernel.π g₂₂) (0 : 0 ⟶ _) :=
    LBC.of_core ⟨kernel.condition _, comp_zero, (is_zero_zero _).eq_of_src _ _, _⟩,
  swap, { simp only [← cancel_epi g₂₁, comp_zero, ← reassoc_of sq₂₁, cokernel.condition] },
  let lbc₃₂ : LBC f₂₁ g₂₁ g₂₂ f₃₁ f₃₂ (cokernel.π g₂₂) 0 (0 : _ ⟶ 0) :=
    LBC.of_core ⟨Hr2.pair.w, cokernel.condition _, sq₂₁, (is_zero_zero _).eq_of_tgt _ _⟩,
  let lbc₄₁ : LBC (kernel.ι f₃₁) 0 0 (0 : 0 ⟶ 0) (0 : 0 ⟶ cokernel g₂₂) 0 0 (0 : 0 ⟶ 0) :=
    LBC.of_core ⟨comp_zero, comp_zero,
      (is_zero_zero _).eq_of_tgt _ _, (is_zero_zero _).eq_of_src _ _⟩,
  have e1 := lbc₁₃.iso_H_to_donᵤ (is_zero_zero _) (is_zero_zero _) (exact_of_zero 0 0),
  have e2 := lbc₁₃.iso_ex_v lbc₂₃ zero_comp zero_comp
    (exact.homology_is_zero _ _ $ exact_zero_left_of_mono _) (Hc2.homology_is_zero _ _),
  have e3 := lbc₂₂.iso_ex_h lbc₂₃ zero_comp (Hr2.drop 1).pair.w
    (Hr1.pair.homology_is_zero _ _) ((Hr1.drop 1).pair.homology_is_zero _ _),
  have e3 := lbc₂₂.iso_ex_v lbc₃₂ zero_comp comp_zero
    (Hc1.homology_is_zero _ _) ((abelian.exact_cokernel _).homology_is_zero _ _),
  have e4 := lbc₃₁.iso_ex_h lbc₃₂ zero_comp zero_comp
    (exact_kernel_ι.homology_is_zero _ _) (Hr2.pair.homology_is_zero _ _),
  have e5 := lbc₃₁.iso_ex_v lbc₄₁ comp_zero comp_zero
    (exact.homology_is_zero _ _ _) ((is_zero_zero _).homology_is_zero _ _ _),
  swap, { rwa ← epi_iff_exact_zero_right, },
  have aux : is_zero lbc₄₁.rcp := (is_zero_zero _).homology_is_zero _ _ _,
  suffices : is_zero lbc₁₃.H, { exact exact_of_homology_is_zero this },
  refine is_zero_of_iso_of_zero aux _,
  resetI,
  exact as_iso (inv (lbc₃₁.ex_v lbc₄₁) ≫ lbc₃₁.ex_h lbc₃₂ ≫ inv (lbc₂₂.ex_v lbc₃₂) ≫
    lbc₂₂.ex_h lbc₂₃ ≫ inv (lbc₁₃.ex_v lbc₂₃) ≫ inv lbc₁₃.H_to_don),
end

-- move me
lemma sq_op (sq : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁) :
  f₂₁.op ≫ g₁₁.op = g₁₂.op ≫ f₁₁.op :=
by simp only [← op_comp, sq]

lemma four_lemma_bot_mono
  (Hr1 : exact_seq 𝓐 [f₂₁, f₂₂, f₂₃]) (Hr2 : exact_seq 𝓐 [f₃₁, f₃₂, f₃₃])
  (Hc1 : exact g₂₂ g₃₂) (Hc2 : exact g₂₃ g₃₃)
  (sq₂₁ : f₂₁ ≫ g₂₂ = g₂₁ ≫ f₃₁) (sq₂₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂)
  (sq₂₃ : f₂₃ ≫ g₂₄ = g₂₃ ≫ f₃₃) (sq₃₂ : f₃₂ ≫ g₃₃ = g₃₂ ≫ f₄₂)
  [epi g₂₁] [mono g₂₄] [epi g₃₂] :
  mono f₄₂ :=
begin
  haveI : epi f₄₂.op := four_lemma_top_epi Hr2.op Hr1.op Hc2.op Hc1.op
    (sq_op sq₃₂) (sq_op sq₂₃) (sq_op sq₂₂) (sq_op sq₂₁),
  exact category_theory.unop_mono_of_epi f₄₂.op
end

lemma four_lemma_left_epi
  (Hc1 : exact_seq 𝓐 [g₁₂, g₂₂, g₃₂]) (Hc2 : exact_seq 𝓐 [g₁₃, g₂₃, g₃₃])
  (Hr1 : exact f₂₁ f₂₂) (Hr2 : exact f₃₁ f₃₂)
  (sq₁₂ : f₁₂ ≫ g₁₃ = g₁₂ ≫ f₂₂)
  (sq₂₁ : f₂₁ ≫ g₂₂ = g₂₁ ≫ f₃₁) (sq₂₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂)
  (sq₃₂ : f₃₂ ≫ g₃₃ = g₃₂ ≫ f₄₂)
  [epi f₁₂] [mono f₄₂] [mono f₃₁] :
  epi g₂₁ :=
four_lemma_top_epi Hc1 Hc2 Hr1 Hr2 sq₂₁.symm sq₁₂.symm sq₂₂.symm sq₃₂.symm

lemma four_lemma_right_mono
  (Hc1 : exact_seq 𝓐 [g₁₂, g₂₂, g₃₂]) (Hc2 : exact_seq 𝓐 [g₁₃, g₂₃, g₃₃])
  (Hr1 : exact f₂₂ f₂₃) (Hr2 : exact f₃₂ f₃₃)
  (sq₁₂ : f₁₂ ≫ g₁₃ = g₁₂ ≫ f₂₂)
  (sq₂₂ : f₂₂ ≫ g₂₃ = g₂₂ ≫ f₃₂) (sq₂₃ : f₂₃ ≫ g₂₄ = g₂₃ ≫ f₃₃)
  (sq₃₂ : f₃₂ ≫ g₃₃ = g₃₂ ≫ f₄₂)
  [epi f₁₂] [mono f₄₂] [epi f₂₃] :
  mono g₂₄ :=
four_lemma_bot_mono Hc1 Hc2 Hr1 Hr2 sq₁₂.symm sq₂₂.symm sq₃₂.symm sq₂₃.symm

end four

end LBC
