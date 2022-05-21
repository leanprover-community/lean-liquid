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

@[reassoc] lemma w (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁ :=
by rw [sq.tr₁, sq.tr₂]

@[reassoc] lemma w_inv [is_iso g₁₁] [is_iso g₁₂] (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  inv g₁₁ ≫ f₁₁ = f₂₁ ≫ inv g₁₂ :=
by rw [is_iso.eq_comp_inv, category.assoc, sq.w, is_iso.inv_hom_id_assoc]

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

lemma ι_eq (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  sq.ι = f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr :=
begin
  rw [← cancel_mono (𝟙 sq.S), ← sq.sum.total],
  simp only [preadditive.add_comp, category.assoc, ι_fst_assoc, ι_snd_assoc, preadditive.comp_add,
    preadditive.add_comp_assoc, sum_str.inl_fst, category.comp_id, sum_str.inr_fst, comp_zero,
    add_zero, sum_str.inl_snd, sum_str.inr_snd, zero_add],
end

lemma π_eq (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  sq.π = sq.sum.fst ≫ g₁₂ + sq.sum.snd ≫ f₂₁ :=
begin
  rw [← cancel_epi (𝟙 sq.S), ← sq.sum.total],
  simp only [preadditive.add_comp, category.assoc, inl_π, inr_π, preadditive.comp_add,
    preadditive.add_comp_assoc, sum_str.inl_fst, category.comp_id, sum_str.inr_fst, comp_zero,
    add_zero, sum_str.inl_snd, sum_str.inr_snd, zero_add],
end

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

lemma of_iso (e₁₁ : A₁₁ ≅ A₃₃) (e₁₂ : A₁₂ ≅ A₃₄) (e₂₁ : A₂₁ ≅ A₄₃) (e₂₂ : A₂₂ ≅ A₄₄)
  (sqa : commsq f₁₁ e₁₁.hom e₁₂.hom f₃₃) (sqb : commsq g₁₁ e₁₁.hom e₂₁.hom g₃₃)
  (sqc : commsq g₁₂ e₁₂.hom e₂₂.hom g₃₄) (sqd : commsq f₂₁ e₂₁.hom e₂₂.hom f₄₃)
  (sq1 : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  commsq f₃₃ g₃₃ g₃₄ f₄₃ :=
of_eq $ by rw [← cancel_epi e₁₁.hom, ← sqa.w_assoc, ← sqc.w, ← sqb.w_assoc, ← sqd.w, sq1.w_assoc]

def kernel (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  commsq (kernel.ι f₁₁) (kernel.map _ _ _ _ sq.w) g₁₁ (kernel.ι f₂₁) :=
commsq.of_eq $ by simp only [kernel.lift_ι]

def cokernel (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  commsq (cokernel.π f₁₁) g₁₂ (cokernel.map _ _ _ _ sq.w) (cokernel.π f₂₁) :=
commsq.of_eq $ by simp only [cokernel.π_desc]

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

lemma bicartesian.of_is_limit_of_is_colimt {sq : commsq f₁₁ g₁₁ g₁₂ f₂₁}
  (hl : is_limit (pullback_cone.mk f₁₁ g₁₁ sq.w)) (hc : is_colimit (pushout_cocone.mk g₁₂ f₂₁ sq.w)) :
  sq.bicartesian :=
begin
  have h : (-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) ≫ sq.π = 0,
  { simp only [sq.w, preadditive.add_comp, preadditive.neg_comp, category.assoc, inl_π, inr_π,
      add_left_neg] },
  let hker : is_limit (kernel_fork.of_ι _ h),
  { fapply is_limit.of_ι,
    { refine λ T g hg, hl.lift (pullback_cone.mk (-g ≫ sq.sum.fst) (g ≫ sq.sum.snd) _),
      rw [sq.π_eq, preadditive.comp_add] at hg,
      simp only [add_eq_zero_iff_eq_neg.1 hg, preadditive.neg_comp, category.assoc,
        neg_neg] },
    { intros T g hg,
      simp only [preadditive.comp_add, preadditive.comp_neg, ← category.assoc],
      erw [hl.fac _ walking_span.left, hl.fac _ walking_span.right],
      simp only [preadditive.neg_comp, category.assoc, neg_neg, pullback_cone.mk_π_app_left,
        pullback_cone.mk_π_app_right, ← preadditive.comp_add, sq.sum.total, category.comp_id] },
    { intros T g hg m hm,
      apply pullback_cone.is_limit.hom_ext hl,
      { erw [pullback_cone.mk_fst, hl.fac _ walking_span.left],
        simp only [← hm, preadditive.neg_comp, category.assoc, neg_neg, pullback_cone.mk_π_app_left,
        preadditive.comp_neg, preadditive.add_comp, sum_str.inl_fst, category.comp_id,
        sum_str.inr_fst, comp_zero, add_zero] },
      { erw [pullback_cone.mk_snd, hl.fac _ walking_span.right],
        simp only [← hm, preadditive.neg_comp, category.assoc, pullback_cone.mk_π_app_right,
          preadditive.add_comp, sum_str.inl_snd, comp_zero, neg_zero, sum_str.inr_snd,
          category.comp_id, zero_add] } } },
  let hcoker : is_colimit (cokernel_cofork.of_π _ h),
  { fapply is_colimit.of_π,
    { refine λ T g hg, hc.desc (pushout_cocone.mk (sq.sum.inl ≫ g) (sq.sum.inr ≫ g) _),
      rwa [preadditive.add_comp, preadditive.neg_comp, add_eq_zero_iff_neg_eq, neg_neg,
        category.assoc, category.assoc] at hg },
    { intros T g hg,
      simp only [sq.π_eq, preadditive.add_comp, category.assoc],
      erw [hc.fac _ walking_cospan.left, hc.fac _ walking_cospan.right],
      simp only [pushout_cocone.mk_ι_app_left, pushout_cocone.mk_ι_app_right, ← category.assoc,
        ← preadditive.add_comp, sq.sum.total, category.id_comp] },
    { intros T g hg m hm,
      apply pushout_cocone.is_colimit.hom_ext hc,
      { erw [pushout_cocone.mk_inl, hc.fac _ walking_cospan.left],
        simp only [← hm, pushout_cocone.mk_ι_app_left, inl_π_assoc] },
      { erw [pushout_cocone.mk_inr, hc.fac _ walking_cospan.right],
        simp only [←hm, pushout_cocone.mk_ι_app_right, inr_π_assoc] } } },
  haveI : mono (-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) := mono_of_is_limit_fork hker,
  haveI : epi sq.π := epi_of_is_colimit_cofork hcoker,
  exact ⟨abelian.exact_of_is_kernel _ _ h hker⟩
end

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

--move this (do we want this?)
instance {C : Type*} [category C] [preadditive C] {X Y : C} : has_neg (X ≅ Y) :=
⟨λ e, ⟨-e.hom, -e.inv, by simp, by simp⟩⟩

@[simp] lemma neg_iso_hom {C : Type*} [category C] [preadditive C] {X Y : C} {e : X ≅ Y} :
  (-e).hom = -(e.hom) := rfl

@[simp] lemma neg_iso_inv {C : Type*} [category C] [preadditive C] {X Y : C} {e : X ≅ Y} :
  (-e).inv = -(e.inv) := rfl

-- move me
@[simp] lemma _root_.category_theory.short_exact.neg_left (h : short_exact f₁₁ f₁₂) :
  short_exact (-f₁₁) f₁₂ :=
begin
  haveI := h.mono, haveI := h.epi,
  refine ⟨_⟩,
  have : -f₁₁ = (-iso.refl _).hom ≫ f₁₁,
  { simp only [neg_iso_hom, iso.refl_hom, category.id_comp, neg_comp], },
  rw [this, exact_iso_comp],
  exact h.exact
end

-- move me
@[simp] lemma _root_.category_theory.short_exact.neg_left_iff :
  short_exact (-f₁₁) f₁₂ ↔ short_exact f₁₁ f₁₂ :=
begin
  refine ⟨_, λ h, h.neg_left⟩,
  intro h, simpa only [neg_neg] using h.neg_left
end

lemma bicartesian.symm {sq : commsq f₁₁ g₁₁ g₁₂ f₂₁} (h : sq.bicartesian) :
  sq.symm.bicartesian :=
begin
  rw bicartesian at h ⊢,
  rw ← category_theory.short_exact.neg_left_iff,
  simp only [neg_add_rev, neg_neg],
  exact h
end

lemma bicartesian.symm_iff (sq : commsq f₁₁ g₁₁ g₁₂ f₂₁) :
  sq.symm.bicartesian ↔ sq.bicartesian :=
⟨λ h, h.symm, λ h, h.symm⟩

section
variables (g₁₁ g₁₂ g₁₃)

-- move me
lemma short_exact.of_iso (h : short_exact f₁₁ f₁₂)
  (sq1 : commsq f₁₁ g₁₁ g₁₂ f₂₁) (sq2 : commsq f₁₂ g₁₂ g₁₃ f₂₂)
  [is_iso g₁₁] [is_iso g₁₂] [is_iso g₁₃] :
  short_exact f₂₁ f₂₂ :=
begin
  have := h.mono, have := h.epi, resetI,
  have : mono f₂₁,
  { suffices : mono (f₂₁ ≫ inv g₁₂), { resetI, apply mono_of_mono f₂₁ (inv g₁₂), },
    rw ← sq1.w_inv, apply_instance },
  have : epi f₂₂,
  { suffices : epi (g₁₂ ≫ f₂₂), { resetI, apply epi_of_epi g₁₂ f₂₂ },
    { rw ← sq2.w, apply epi_comp } },
  resetI, refine ⟨_⟩,
  apply exact_of_iso_of_exact' _ _ _ _ (as_iso g₁₁) (as_iso g₁₂) (as_iso g₁₃)
    sq1.symm.w sq2.symm.w h.exact,
end

end

lemma bicartesian.of_iso (e₁₁ : A₁₁ ≅ A₃₃) (e₁₂ : A₁₂ ≅ A₃₄) (e₂₁ : A₂₁ ≅ A₄₃) (e₂₂ : A₂₂ ≅ A₄₄)
  {sq1 : commsq f₁₁ g₁₁ g₁₂ f₂₁} {sq2 : commsq f₃₃ g₃₃ g₃₄ f₄₃}
  (sqa : commsq f₁₁ e₁₁.hom e₁₂.hom f₃₃) (sqb : commsq g₁₁ e₁₁.hom e₂₁.hom g₃₃)
  (sqc : commsq g₁₂ e₁₂.hom e₂₂.hom g₃₄) (sqd : commsq f₂₁ e₂₁.hom e₂₂.hom f₄₃)
  (h : sq1.bicartesian) :
  sq2.bicartesian :=
begin
  let e : sq1.S ≅ sq2.S := _,
  apply short_exact.of_iso e₁₁.hom e.hom e₂₂.hom h,
  swap 3,
  { refine ⟨sq1.sum.fst ≫ e₁₂.hom ≫ sq2.sum.inl + sq1.sum.snd ≫ e₂₁.hom ≫ sq2.sum.inr,
            sq2.sum.fst ≫ e₁₂.inv ≫ sq1.sum.inl + sq2.sum.snd ≫ e₂₁.inv ≫ sq1.sum.inr,
            _, _⟩;
    { dsimp, simp only [comp_add, add_comp_assoc, category.assoc, sum_str.inl_fst,
        category.comp_id, sum_str.inr_fst, comp_zero, add_zero, iso.hom_inv_id_assoc,
        sum_str.inl_snd, sum_str.inr_snd, zero_add, sq1.sum.total, sq2.sum.total,
        iso.inv_hom_id_assoc], }, },
  { apply commsq.of_eq, dsimp,
    simp only [comp_add, add_comp_assoc, neg_comp, category.assoc, sum_str.inl_fst,
      category.comp_id, sum_str.inr_fst, comp_zero, add_zero, sum_str.inl_snd, neg_zero,
      sum_str.inr_snd, zero_add, comp_neg, sqa.w_assoc, sqb.w_assoc], },
  { apply commsq.of_eq, dsimp,
    simp only [add_comp, category.assoc, inl_π, inr_π, ← sqc.w, ← sqd.w, sq1.π_eq], }
end

end commsq
