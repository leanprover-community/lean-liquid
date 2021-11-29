import algebra.homology.exact
import category_theory.abelian.basic

noncomputable theory

universes v u

open category_theory category_theory.limits category_theory.preadditive

variables {𝒜 : Type*} [category 𝒜]

namespace category_theory

variables [abelian 𝒜]
variables {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C)

structure short_exact : Prop :=
[mono  : mono f]
[epi   : epi g]
[exact : exact f g]

/-- An exact sequence `A -f⟶ B -g⟶ C` is *left split*
if there exists a morphism `φ : B ⟶ A` such that `f ≫ φ = 𝟙 A` and `g` is epi.

Such a sequence is automatically short exact (i.e., `f` is mono). -/
structure left_split : Prop :=
(left_split : ∃ φ : B ⟶ A, f ≫ φ = 𝟙 A)
[epi   : epi g]
[exact : exact f g]

lemma left_split.short_exact {f : A ⟶ B} {g : B ⟶ C} (h : left_split f g) : short_exact f g :=
{ mono :=
  begin
    obtain ⟨φ, hφ⟩ := h.left_split,
    haveI : mono (f ≫ φ) := by { rw hφ, apply_instance },
    exact mono_of_mono f φ,
  end,
  epi := h.epi,
  exact := h.exact }

/-- An exact sequence `A -f⟶ B -g⟶ C` is *right split*
if there exists a morphism `φ : C ⟶ B` such that `f ≫ φ = 𝟙 A` and `f` is mono.

Such a sequence is automatically short exact (i.e., `g` is epi). -/
structure right_split : Prop :=
(right_split : ∃ χ : C ⟶ B, χ ≫ g = 𝟙 C)
[mono  : mono f]
[exact : exact f g]

lemma right_split.short_exact {f : A ⟶ B} {g : B ⟶ C} (h : right_split f g) : short_exact f g :=
{ epi :=
  begin
    obtain ⟨χ, hχ⟩ := h.right_split,
    haveI : epi (χ ≫ g) := by { rw hχ, apply_instance },
    exact epi_of_epi χ g,
  end,
  mono := h.mono,
  exact := h.exact }

/-- An exact sequence `A -f⟶ B -g⟶ C` is *split* if there exist
`φ : B ⟶ A` and `χ : C ⟶ B` such that:
* `f ≫ φ = 𝟙 A`
* `χ ≫ g = 𝟙 C`
* `f ≫ g = 0`
* `χ ≫ φ = 0`
* `φ ≫ f + g ≫ χ = 𝟙 B`

Such a sequence is automatically short exact (i.e., `f` is mono and `g` is epi). -/
structure split : Prop :=
(split : ∃ (φ : B ⟶ A) (χ : C ⟶ B),
  f ≫ φ = 𝟙 A ∧ χ ≫ g = 𝟙 C ∧ f ≫ g = 0 ∧ χ ≫ φ = 0 ∧ φ ≫ f + g ≫ χ = 𝟙 B)

/-- A *splitting* of a sequence `A -f⟶ B -g⟶ C` is an isomorphism
to the short exact sequence `0 ⟶ A ⟶ A ⊕ C ⟶ C ⟶ 0` such that
the vertical maps on the left and the right are the identity. -/
structure splitting :=
(iso : B ≅ A ⊞ C)
(comp_iso_eq_inl : f ≫ iso.hom = biprod.inl)
(iso_comp_snd_eq : iso.hom ≫ biprod.snd = g)

namespace splitting

attribute [simp, reassoc] comp_iso_eq_inl iso_comp_snd_eq

variables {f g}

@[simp, reassoc] lemma inl_comp_iso_eq (h : splitting f g) : biprod.inl ≫ h.iso.inv = f :=
by rw [iso.comp_inv_eq, h.comp_iso_eq_inl]

@[simp, reassoc] lemma iso_comp_eq_snd (h : splitting f g) : h.iso.inv ≫ g = biprod.snd :=
by rw [iso.inv_comp_eq, h.iso_comp_snd_eq]

lemma split (h : splitting f g) : split f g :=
begin
  let φ := h.iso.hom ≫ biprod.fst,
  let χ := biprod.inr ≫ h.iso.inv,
  refine ⟨⟨φ, χ, _, _, _, _, _⟩⟩,
  { rw [h.comp_iso_eq_inl_assoc, biprod.inl_fst], },
  { rw [category.assoc, iso_comp_eq_snd, biprod.inr_snd], },
  { rw [← h.inl_comp_iso_eq, category.assoc, h.iso_comp_eq_snd, biprod.inl_snd], },
  { simp only [iso.inv_hom_id_assoc, biprod.inr_fst, category.assoc], },
  { rw [← cancel_mono h.iso.hom, ← cancel_epi h.iso.inv],
    simp only [comp_add, add_comp, category.assoc, iso.inv_hom_id_assoc, biprod.total,
      category.id_comp, category.comp_id, comp_iso_eq_inl, iso_comp_eq_snd_assoc, iso.inv_hom_id], }
end

lemma exact_of_split {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (χ : C ⟶ B) (φ : B ⟶ A)
  (hfg : f ≫ g = 0) (H : φ ≫ f + g ≫ χ = 𝟙 B) : exact f g :=
{ w := hfg,
  epi :=
  begin
    let ψ : (kernel_subobject g : 𝒜) ⟶ image_subobject f :=
      subobject.arrow _ ≫ φ ≫ factor_thru_image_subobject f,
    suffices : ψ ≫ image_to_kernel f g hfg = 𝟙 _,
    { convert epi_of_epi ψ _, rw this, apply_instance },
    rw ← cancel_mono (subobject.arrow _), swap, { apply_instance },
    simp only [image_to_kernel_arrow, image_subobject_arrow_comp, category.id_comp, category.assoc],
    calc (kernel_subobject g).arrow ≫ φ ≫ f
        = (kernel_subobject g).arrow ≫ 𝟙 B : _
    ... = (kernel_subobject g).arrow        : category.comp_id _,
    rw [← H, preadditive.comp_add],
    simp only [add_zero, zero_comp, kernel_subobject_arrow_comp_assoc],
  end }

-- move this
instance exact_inl_snd (A B : 𝒜) : exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
exact_of_split _ _ biprod.inr biprod.fst biprod.inl_snd biprod.total

lemma short_exact (h : splitting f g) : short_exact f g :=
{ mono := by { rw ← h.inl_comp_iso_eq, exact mono_comp _ _ },
  epi := by { rw ← h.iso_comp_snd_eq, exact epi_comp _ _ },
  exact :=
  begin
    rw exact_iff_exact_of_iso f g (biprod.inl : A ⟶ A ⊞ C) (biprod.snd : A ⊞ C ⟶ C) _ _ _,
    { apply_instance },
    { refine arrow.iso_mk (iso.refl _) h.iso _,
      simp only [iso.refl_hom, arrow.mk_hom, category.id_comp, comp_iso_eq_inl], },
    { refine arrow.iso_mk h.iso (iso.refl _) _,
      simp only [iso.refl_hom, arrow.mk_hom, category.comp_id, iso_comp_snd_eq],
      erw category.comp_id /- why ?? -/ },
    { refl }
  end }


-- TODO: this should be generalized to isoms of short sequences,
-- because now it forces one direction, and we want both.
/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : B ⟶ A ⊞ C` such that `f ≫ i` is the canonical map `A ⟶ A ⊞ C` and
`i ≫ q = g`, where `q` is the canonical map `A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is than automatically an isomorphism. -/
def mk' (i : B ⟶ A ⊞ C) (h1 : f ≫ i = biprod.inl) (h2 : i ≫ biprod.snd = g) :
  splitting f g :=
{ iso :=
  begin
    refine @as_iso _ _ _ _ i (id _),
    -- use five lemma, or snake lemma, or whatever
    sorry
  end,
  comp_iso_eq_inl := by { rwa as_iso_hom, },
  iso_comp_snd_eq := h2 }

end splitting

/-- A short exact sequence that is left split admits a splitting. -/
def left_split.splitting {f : A ⟶ B} {g : B ⟶ C} (h : left_split f g) : splitting f g :=
splitting.mk' (biprod.lift h.left_split.some g)
(by { ext,
  { simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.left_split.some_spec },
  { simp only [biprod.inl_snd, biprod.lift_snd, category.assoc, h.exact.w], } })
(by { simp only [biprod.lift_snd], })


end category_theory
