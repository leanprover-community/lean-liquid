import for_mathlib.homology_exact
import for_mathlib.split_exact
import for_mathlib.sum_str
.

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

section

variables (f₁₁ g₁₁ g₁₂ f₂₁)

/-- A *commutative square* is a commutative diagram of the following shape:
```
A₁₁ --- f₁₁ --> A₁₂
 |               |
g₁₁             g₁₂
 |               |
 v               v
A₂₁ --- f₂₁ --> A₂₂
```
The order of (explicit) variables is: top-to-bottom, left-to-right,
alternating between rows of horizontal maps and rows of vertical maps. -/
@[ext] structure commsq :=
(S : 𝓐)
(ι : A₁₁ ⟶ S)
(π : S ⟶ A₂₂)
(diag : A₁₁ ⟶ A₂₂)
(sum : sum_str A₁₂ A₂₁ S)
(ι_fst : ι ≫ sum.fst = f₁₁)
(ι_snd : ι ≫ sum.snd = g₁₁)
(inl_π : sum.inl ≫ π = g₁₂)
(inr_π : sum.inr ≫ π = f₂₁)
(tr₁ : g₁₁ ≫ f₂₁ = diag)
(tr₂ : f₁₁ ≫ g₁₂ = diag)

end

namespace commsq

attribute [simp, reassoc] ι_fst ι_snd inl_π inr_π

lemma w (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁ :=
by rw [sq.tr₁, sq.tr₂]

def of_eq (w : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁) : commsq f₁₁ g₁₁ g₁₂ f₂₁ :=
{ S := A₁₂ ⊞ A₂₁,
  ι := biprod.lift f₁₁ g₁₁,
  π := biprod.desc g₁₂ f₂₁,
  diag := g₁₁ ≫ f₂₁,
  sum := sum_str.biprod _ _,
  ι_fst := biprod.lift_fst _ _,
  ι_snd := biprod.lift_snd _ _,
  inl_π := biprod.inl_desc _ _,
  inr_π := biprod.inr_desc _ _,
  tr₁ := rfl,
  tr₂ := w }

def symm (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) : commsq g₁₁ f₁₁ f₂₁ g₁₂ :=
{ sum := sq.sum.symm,
  ι_fst := sq.ι_snd,
  ι_snd := sq.ι_fst,
  inl_π := sq.inr_π,
  inr_π := sq.inl_π,
  tr₁ := sq.tr₂,
  tr₂ := sq.tr₁,
  .. sq }

section iso
open category_theory.preadditive

lemma ι_iso_hom (sq₁ sq₂ : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  sq₁.ι ≫ (sq₁.sum.iso sq₂.sum).hom = sq₂.ι :=
begin
  simp only [sum_str.iso_hom, comp_add, ι_fst_assoc, ι_snd_assoc],
  simp only [← sq₂.ι_fst_assoc, ← sq₂.ι_snd_assoc, ← comp_add, sum_str.total, category.comp_id],
end

lemma iso_hom_π (sq₁ sq₂ : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  (sq₁.sum.iso sq₂.sum).hom ≫ sq₂.π = sq₁.π :=
begin
  simp only [sum_str.iso_hom, add_comp, category.assoc, inl_π, inr_π],
  simp only [← sq₁.inl_π, ← sq₁.inr_π],
  simp only [← category.assoc, ← add_comp, sum_str.total, category.id_comp],
end

lemma ι_iso_inv (sq₁ sq₂ : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  sq₂.ι ≫ (sq₁.sum.iso sq₂.sum).inv = sq₁.ι :=
ι_iso_hom _ _

lemma iso_inv_π (sq₁ sq₂ : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  (sq₁.sum.iso sq₂.sum).inv ≫ sq₁.π = sq₂.π :=
iso_hom_π _ _

end iso

def bicartesian (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) : Prop :=
short_exact (-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) sq.π

def bicartesian.is_limit {sq : commsq f₁₁ g₁₁ g₁₂ f₂₁} (h : sq.bicartesian) :
  is_limit (pullback_cone.mk f₁₁ g₁₁ sq.w) :=
pullback_cone.is_limit.mk sq.w
  (λ s, (@abelian.is_limit_of_exact_of_mono _ _ _ _ _ _ _ _ h.mono h.exact).lift
      (fork.of_ι (-s.fst ≫ sq.sum.inl + s.snd ≫ sq.sum.inr)
        (by simp only [s.condition, preadditive.add_comp, preadditive.neg_comp, category.assoc,
          inl_π, inr_π, add_left_neg, comp_zero])))
  (λ s,
  begin
    have : f₁₁ = -((-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) ≫ sq.sum.fst),
    { simp only [preadditive.add_comp, preadditive.neg_comp, category.assoc, sum_str.inl_fst,
        category.comp_id, sum_str.inr_fst, comp_zero, add_zero, neg_neg] },
    conv_lhs { congr, skip, rw this },
    rw [preadditive.comp_neg, ← category.assoc],
    erw (@abelian.is_limit_of_exact_of_mono _ _ _ _ _ _ _ _ h.mono h.exact).fac _
      walking_parallel_pair.zero,
    simp only [preadditive.add_comp, preadditive.neg_comp, category.assoc, comp_zero,
      fork.of_ι_π_app, sum_str.inl_fst, category.comp_id, sum_str.inr_fst, add_zero, neg_neg],
  end)
  (λ s,
  begin
    have : g₁₁ = (-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) ≫ sq.sum.snd,
    { simp only [preadditive.add_comp, preadditive.neg_comp, category.assoc, sum_str.inl_snd,
        comp_zero, neg_zero, sum_str.inr_snd, category.comp_id, zero_add] },
    conv_lhs { congr, skip, rw this },
    rw ← category.assoc,
    erw (@abelian.is_limit_of_exact_of_mono _ _ _ _ _ _ _ _ h.mono h.exact).fac _
      walking_parallel_pair.zero,
    simp only [preadditive.add_comp, preadditive.neg_comp, category.assoc, comp_zero,
      fork.of_ι_π_app, sum_str.inl_snd, neg_zero, sum_str.inr_snd, category.comp_id, zero_add],
  end)
  (λ s m h₁ h₂,
  begin
    apply fork.is_limit.hom_ext (@abelian.is_limit_of_exact_of_mono _ _ _ _ _ _ _ _ h.mono h.exact),
    erw [is_limit.fac],
    simp only [reassoc_of h₁, reassoc_of h₂, kernel_fork.ι_of_ι, preadditive.comp_add,
      preadditive.comp_neg, fork.of_ι_π_app],
  end)

def bicartesian.is_colimit {sq : commsq f₁₁ g₁₁ g₁₂ f₂₁} (h : sq.bicartesian) :
  is_colimit (pushout_cocone.mk g₁₂ f₂₁ sq.w) :=
pushout_cocone.is_colimit.mk sq.w
  (λ s, (@abelian.is_colimit_of_exact_of_epi _ _ _ _ _ _ _ _ h.epi h.exact).desc
    (cofork.of_π (sq.sum.fst ≫ s.inl + sq.sum.snd ≫ s.inr)
      (by simp only [s.condition, preadditive.comp_add, preadditive.add_comp_assoc,
        preadditive.neg_comp, category.assoc, sum_str.inl_fst, category.comp_id, sum_str.inr_fst,
        comp_zero, add_zero, sum_str.inl_snd, neg_zero, sum_str.inr_snd, zero_add, add_left_neg,
        zero_comp])))
  (λ s,
  begin
    conv_lhs { congr, rw [← sq.inl_π] },
    rw category.assoc,
    erw (@abelian.is_colimit_of_exact_of_epi _ _ _ _ _ _ _ _ h.epi h.exact).fac _
      walking_parallel_pair.one,
    simp only [preadditive.comp_add, add_zero, zero_comp, cofork.of_π_ι_app, sum_str.inl_fst_assoc,
      sum_str.inl_snd_assoc],
  end)
  (λ s,
  begin
    conv_lhs { congr, rw [← sq.inr_π] },
    rw category.assoc,
    erw (@abelian.is_colimit_of_exact_of_epi _ _ _ _ _ _ _ _ h.epi h.exact).fac _
      walking_parallel_pair.one,
    simp only [preadditive.comp_add, zero_add, zero_comp, cofork.of_π_ι_app, sum_str.inr_fst_assoc,
      sum_str.inr_snd_assoc]
  end)
  (λ s m h₁ h₂,
  begin
    apply cofork.is_colimit.hom_ext
      (@abelian.is_colimit_of_exact_of_epi _ _ _ _ _ _ _ _ h.epi h.exact),
    erw [is_colimit.fac],
    simp only [cokernel_cofork.π_of_π, cofork.of_π_ι_app],
    conv_lhs { congr, rw [← category.id_comp sq.π] },
    rw [← sq.sum.total],
    simp only [h₁, h₂, preadditive.add_comp, category.assoc, inl_π, inr_π]
  end)

open category_theory.preadditive

lemma bicartesian.congr {sq₁ : commsq f₁₁ g₁₁ g₁₂ f₂₁}
  (h : sq₁.bicartesian) (sq₂ : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  sq₂.bicartesian :=
begin
  have := h.mono, have := h.epi, resetI,
  have hm : mono (-f₁₁ ≫ sq₂.sum.inl + g₁₁ ≫ sq₂.sum.inr),
  { suffices : -f₁₁ ≫ sq₂.sum.inl + g₁₁ ≫ sq₂.sum.inr =
      (-f₁₁ ≫ sq₁.sum.inl + g₁₁ ≫ sq₁.sum.inr) ≫ (sq₁.sum.iso sq₂.sum).hom,
    { rw [this], apply mono_comp },
    simp only [sum_str.iso_hom, comp_add, add_comp_assoc, neg_comp, category.assoc,
      sum_str.inl_fst, category.comp_id, sum_str.inr_fst, comp_zero, add_zero,
      sum_str.inl_snd, neg_zero, sum_str.inr_snd, zero_add], },
  have he : epi sq₂.π, { rw [← sq₁.iso_inv_π sq₂], apply epi_comp },
  have H : exact (-f₁₁ ≫ sq₂.sum.inl + g₁₁ ≫ sq₂.sum.inr) sq₂.π,
  { apply exact_of_iso_of_exact' _ _ _ _
      (iso.refl _) (sq₁.sum.iso sq₂.sum) (iso.refl _) _ _ h.exact,
    { simp only [iso.refl_hom, comp_add, category.id_comp, sum_str.iso_hom, add_comp_assoc,
        neg_comp, category.assoc, sum_str.inl_fst, sum_str.inr_fst, comp_zero, add_zero,
        sum_str.inl_snd, neg_zero, sum_str.inr_snd, zero_add], },
    { simp only [iso.refl_hom, category.comp_id, iso_hom_π], }, },
  exactI ⟨H⟩
end

lemma bicartesian_iff (sq₁ sq₂ : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  sq₁.bicartesian ↔ sq₂.bicartesian :=
⟨λ h, h.congr _, λ h, h.congr _⟩

end commsq
