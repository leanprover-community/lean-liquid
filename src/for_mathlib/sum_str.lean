import category_theory.abelian.opposite

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

attribute [simp, reassoc] sum_str.inl_fst sum_str.inr_snd sum_str.inl_snd sum_str.inr_fst

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

open category_theory.preadditive opposite

section iso

variables {X₁ X₂ : 𝓐} (S₁ : sum_str A B X₁) (S₂ : sum_str A B X₂)

@[simps]
def iso : X₁ ≅ X₂ :=
{ hom := S₁.fst ≫ S₂.inl + S₁.snd ≫ S₂.inr,
  inv := S₂.fst ≫ S₁.inl + S₂.snd ≫ S₁.inr,
  hom_inv_id' := by simp only [comp_add, add_comp_assoc, category.assoc, add_comp, inl_fst_assoc,
    inl_snd_assoc, zero_comp, comp_zero, add_zero, inr_fst_assoc, inr_snd_assoc, zero_add, total],
  inv_hom_id' := by simp only [comp_add, add_comp_assoc, category.assoc, add_comp, inl_fst_assoc,
    inl_snd_assoc, zero_comp, comp_zero, add_zero, inr_fst_assoc, inr_snd_assoc, zero_add, total], }

end iso

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
