import category_theory.preadditive
import category_theory.abelian.exact
import algebra.homology.exact


namespace category_theory

open category_theory.limits

variables {C : Type*} [category C] [has_zero_morphisms C]

structure is_zero (X : C) : Prop :=
(eq_zero_of_src : ∀ {Y : C} (f : X ⟶ Y), f = 0)
(eq_zero_of_tgt : Π {Y : C} (f : Y ⟶ X), f = 0)

def is_zero.eq_of_src {C : Type*} [category C] [has_zero_morphisms C] {X Y : C}
  (hX : is_zero X) (f g : X ⟶ Y) : f = g :=
(hX.eq_zero_of_src f).trans (hX.eq_zero_of_src g).symm

def is_zero.eq_of_tgt {C : Type*} [category C] [has_zero_morphisms C] {X Y : C}
  (hX : is_zero X) (f g : Y ⟶ X) : f = g :=
(hX.eq_zero_of_tgt f).trans (hX.eq_zero_of_tgt g).symm

def is_zero.iso {C : Type*} [category C] [has_zero_morphisms C] {X Y : C}
  (hX : is_zero X) (hY : is_zero Y) : X ≅ Y :=
{ hom := 0,
  inv := 0,
  hom_inv_id' := hX.eq_of_src _ _,
  inv_hom_id' := hY.eq_of_src _ _, }

open_locale zero_object

lemma is_zero_zero (C : Type*) [category C] [has_zero_morphisms C] [has_zero_object C] :
  is_zero (0 : C) :=
{ eq_zero_of_src := λ Y f, by ext,
  eq_zero_of_tgt := λ Y f, by ext }

def is_zero.iso_zero {C : Type*} [category C] [has_zero_morphisms C] [has_zero_object C]
  {X : C} (hX : is_zero X) : X ≅ 0 :=
hX.iso (is_zero_zero C)

lemma is_zero_of_top_le_bot [has_zero_object C] (X : C)
  (h : (⊤ : subobject X) ≤ ⊥) : is_zero X :=
{ eq_zero_of_src := λ Y f,
  begin
    rw [← cancel_epi ((⊤ : subobject X).arrow), ← subobject.of_le_arrow h],
    simp only [subobject.bot_arrow, comp_zero, zero_comp],
  end,
  eq_zero_of_tgt := λ Y f,
  begin
    rw ← subobject.bot_factors_iff_zero,
    exact subobject.factors_of_le f h (subobject.top_factors f),
  end }

lemma is_zero_of_iso_of_zero {C : Type*} [category C] [has_zero_morphisms C]
  {X : C} (hX : is_zero X) {Y : C} (h : X ≅ Y) : is_zero Y :=
begin
  refine ⟨λ Z f, _, λ Z f, _⟩,
  { have : h.inv ≫ (h.hom ≫ f) = 0,
    { rw [hX.eq_zero_of_src (h.hom ≫ f), comp_zero] },
    simpa using this },
  { have : (f ≫ h.inv) ≫ h.hom = 0,
    { rw [hX.eq_zero_of_tgt (f ≫ h.inv), zero_comp] },
    simpa using this }
end

lemma is_zero_of_exact_zero_zero {C : Type*} [category C] [abelian C]
  {X Y Z : C} (h : exact (0 : X ⟶ Y) (0 : Y ⟶ Z)) : is_zero Y :=
is_zero_of_top_le_bot _
begin
  rw abelian.exact_iff_image_eq_kernel at h,
  rw [← @kernel_subobject_zero _ _ _ Y Z, ← @image_subobject_zero _ _ _ _ X Y, h],
end

lemma is_zero_of_exact_zero_zero' {C : Type*} [category C] [abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : exact f g) (hf : f = 0) (hg : g = 0) : is_zero Y :=
by { rw [hf, hg] at h, exact is_zero_of_exact_zero_zero h }

lemma is_zero_cokernel_of_epi {C : Type*} [category C] [abelian C] {X Y : C}
  (f : X ⟶ Y) [epi f] : is_zero (cokernel f) :=
begin
  have h1 : cokernel.π f = 0, by rwa ← abelian.epi_iff_cokernel_π_eq_zero,
  have h2 : exact (cokernel.π f) 0 := category_theory.exact_epi_zero (cokernel.π f),
  exact is_zero_of_exact_zero_zero' (cokernel.π f) 0 h2 h1 rfl,
end

lemma epi_iff_is_zero_cokernel {C : Type*} [category C] [abelian C] {X Y : C}
  (f : X ⟶ Y) : epi f ↔ is_zero (cokernel f) :=
begin
  split,
  { introsI, apply is_zero_cokernel_of_epi },
  { intros h,
    rw abelian.epi_iff_cokernel_π_eq_zero,
    apply h.eq_zero_of_tgt }
end

lemma is_zero_kernel_of_mono {C : Type*} [category C] [abelian C] {X Y : C}
  (f : X ⟶ Y) [mono f] : is_zero (kernel f) :=
begin
  have h1 : kernel.ι f = 0, by rwa ← abelian.mono_iff_kernel_ι_eq_zero,
  have h2 : exact 0 (kernel.ι f) := category_theory.exact_zero_mono (kernel.ι f),
  exact is_zero_of_exact_zero_zero' 0 (kernel.ι f) h2 rfl h1
end

lemma mono_iff_is_zero_kernel {C : Type*} [category C] [abelian C] {X Y : C}
  (f : X ⟶ Y) : mono f ↔ is_zero (kernel f) :=
begin
  split,
  { introsI, apply is_zero_kernel_of_mono },
  { intros h,
    rw abelian.mono_iff_kernel_ι_eq_zero,
    apply h.eq_zero_of_src }
end

class preserves_zero_objects {C D : Type*} [category C] [has_zero_morphisms C]
  [category D] [has_zero_morphisms D] (F : C ⥤ D) : Prop :=
(preserves : ∀ (X : C), is_zero X → is_zero (F.obj X))

lemma is_zero_of_preserves {C D : Type*} [category C] [has_zero_morphisms C]
  [category D] [has_zero_morphisms D] {X : C} (F : C ⥤ D)
  [preserves_zero_objects F] (e : is_zero X) : is_zero (F.obj X) :=
preserves_zero_objects.preserves _ e

end category_theory
