import algebra.homology.homological_complex
import algebra.homology.single
import category_theory.abelian.basic

import for_mathlib.split_exact
import for_mathlib.derived.defs
import for_mathlib.has_homology

noncomputable theory

open category_theory category_theory.limits

namespace cochain_complex

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables (C : cochain_complex 𝓐 ℤ)


local attribute [instance] has_zero_object.has_zero -- isn't there a locale which does this??

/--
Given a cochain complex
```
C^{n-2} → C^{n-1} → C^n → C^{n+1}
```
`imker C n` should be the cochain complex
```
   0  → Im(d^{n-1}) → Ker(d^n) → 0
```
supported in degrees n-1 and n (note that both terms are naturally subobjects
of C^n). As a result, `H_i(imker C n) = 0` for all `i≠n`, and `= H_i(C)` for `i=n`.
-/
def imker (C : cochain_complex 𝓐 ℤ) (n : ℤ) : cochain_complex 𝓐 ℤ :=
{ X := λ i, if i = n-1 then image_subobject (C.d_to n) else
  if i = n then kernel_subobject (C.d_from n) else 0,
  d := λ i j, if hi : i = n - 1 then if hj : j = n then
    (eq_to_iso (by rw [hi, if_pos rfl]) : ((if i = n-1 then image_subobject (C.d_to n) else
  if i = n then kernel_subobject (C.d_from n) else 0) : 𝓐) ≅ image_subobject (C.d_to n)).hom ≫
    image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n) ≫
            (eq_to_iso begin rw [if_neg, if_pos hj], linarith, end :
              (kernel_subobject (C.d_from n) : 𝓐) ≅ _).hom
          else 0
        else 0,
  shape' := begin
    rintro i j (h : _ ≠ _),
    split_ifs with hi,
    { rw dif_neg,
      rintro rfl,
      exact (h (add_eq_of_eq_sub hi)).elim, },
    { refl },
  end,
  d_comp_d' := begin
    rintro i j k (rfl : _ = _) (rfl : _ = _),
    split_ifs with hi hn,
    { subst hi,
      simp only [add_right_eq_self, one_ne_zero, not_false_iff, dif_neg, comp_zero]},
    { apply zero_comp, },
  end }

namespace imker

open homological_complex (single)

lemma X_def {n i : ℤ} : (imker C n).X i =
if i = n-1 then image_subobject (C.d_to n) else
  if i = n then kernel_subobject (C.d_from n) else
    (has_zero_object.has_zero 𝓐).zero :=
rfl

@[simps] def X_iso_image (n : ℤ) : (imker C n).X (n-1) ≅ image_subobject (C.d_to n) :=
eq_to_iso (by {rw [X_def, if_pos rfl]})

@[simps] def X_iso_image_of_eq {n i : ℤ} (h : i = n - 1) :
  (imker C n).X i ≅ image_subobject (C.d_to n) :=
eq_to_iso (by {rw [X_def, if_pos h]})

@[simps] def X_iso_kernel (n : ℤ) : (imker C n).X n ≅ kernel_subobject (C.d_from n) :=
eq_to_iso (by {rw [X_def, if_neg, if_pos rfl], linarith})

@[simps] def X_iso_kernel_of_eq {n i : ℤ} (h : i = n) :
  (imker C n).X i ≅ kernel_subobject (C.d_from n) :=
eq_to_iso (by {rw [X_def, if_neg, if_pos h], linarith})

@[simps] def kernel_iso_X_of_eq {n i : ℤ} (h : i = n) :
  (kernel_subobject (C.d_from n) : 𝓐) ≅ (imker C n).X i :=
eq_to_iso (by {rw [X_def, if_neg, if_pos h], linarith})

lemma X_is_zero_of_ne {i j : ℤ} (h1 : j ≠ i - 1) (h2 : j ≠ i) : is_zero ((C.imker i).X j) :=
begin
  rw [X_def, if_neg h1, if_neg h2],
  exact is_zero_zero 𝓐,
end

@[simp] lemma d_def {n i j : ℤ} : (imker C n).d i j = if hi : i = n - 1 then if hj : j = n then
    (eq_to_iso (by rw [hi, if_pos rfl]) : ((if i = n-1 then image_subobject (C.d_to n) else
  if i = n then kernel_subobject (C.d_from n) else 0) : 𝓐) ≅ image_subobject (C.d_to n)).hom ≫
    image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n) ≫
            (eq_to_iso begin dsimp only [imker], rw [if_neg, if_pos hj], linarith, end :
              (kernel_subobject (C.d_from n) : 𝓐) ≅ _).hom
          else 0
        else 0 :=
rfl

lemma d_eq_im_to_ker {n i j : ℤ} (h : i = n - 1) (hj : j = n) : (imker C n).d i j =
(X_iso_image_of_eq C h).hom ≫
image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n) ≫ (X_iso_kernel_of_eq _ hj).inv :=
begin
  simp only [h, hj, eq_self_iff_true, d_def, eq_to_iso.hom, dif_pos, X_iso_image_of_eq_hom,
    X_iso_kernel_of_eq_inv],
  refl,
end

lemma d_from_eq_zero {n i : ℤ} (h : i ≠ n - 1) : (C.imker n).d_from i = 0 :=
begin
  rw [homological_complex.d_from_eq (C.imker n) rfl, d_def, dif_neg h, zero_comp],
end

lemma bounded_by (i : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.imker i)).bounded_by (i+1) :=
begin
  intros j hj,
  simp only [homotopy_category.quotient_obj_as],
  apply X_is_zero_of_ne;
  linarith,
end

instance is_bounded_above (i : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.imker i)).is_bounded_above :=
⟨⟨i+1, bounded_by C i⟩⟩

/-- The natural map from `imker C n` to `H_n(C)[n]`, the complex consisting of the n'th
homology of C supported in degree n. -/
def to_single (n : ℤ) : C.imker n ⟶ (single _ _ n).obj (C.homology n) :=
{ f := λ i, if h : i = n then (X_iso_kernel_of_eq C h).hom ≫
  cokernel.π (image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n)) ≫
 (homological_complex.single_obj_X_self 𝓐 (complex_shape.up ℤ) n _).inv ≫
 (eq_to_iso (begin rw h, refl, end)).hom else 0,
  comm' := begin
   rintro i j (rfl : _ = _),
   simp only [homological_complex.single_obj_X_self_inv, eq_to_iso.hom, eq_to_hom_trans,
     homological_complex.single_obj_d, comp_zero],
   split_ifs with hi hn,
   { subst hi, clear hn,
     rw d_eq_im_to_ker C (show i = i + 1 - 1, by ring) rfl,
     simp only [category.assoc, iso.inv_hom_id_assoc, cokernel.condition_assoc, zero_comp,
       comp_zero], },
   { exact (hn rfl).elim },
   { rw comp_zero },
  end }

-- move
lemma is_iso_of_is_zero_of_is_zero {a b : 𝓐} (ha : is_zero a) (hb : is_zero b)
  (f : a ⟶ b) : is_iso f :=
begin
  rw is_zero.eq_zero_of_src ha f,
  apply (is_iso_zero_equiv a b).symm.to_fun,
  exact ⟨is_zero.eq_of_src ha (𝟙 a) 0, is_zero.eq_of_src hb (𝟙 b) 0⟩,
end

-- move
lemma obj_is_zero_of_iso {𝓑 : Type*} [category 𝓑] [abelian 𝓑] {F G : 𝓐 ⥤ 𝓑}
  (h : F ≅ G) {a : 𝓐} (ha : is_zero (F.obj a)) : is_zero (G.obj a) :=
is_zero_of_iso_of_zero ha (h.app a)

-- move
lemma map_is_iso_of_iso_of_map_is_iso {𝓑 : Type*} [category 𝓑] [abelian 𝓑] {F G : 𝓐 ⥤ 𝓑}
  (h : F ≅ G) {a₁ a₂ : 𝓐} (f : a₁ ⟶ a₂) (ha : is_iso (F.map f)) : is_iso (G.map f) :=
begin
  rw ← nat_iso.naturality_1 h,
  exact is_iso.comp_is_iso,
end

-- move
lemma _root_.homological_complex.single_obj_is_zero (V : Type*) [_inst_1 : category V]
  [_inst_2 : has_zero_morphisms V] [_inst_3 : has_zero_object V] {ι : Type*}
  [_inst_4 : decidable_eq ι] (c : complex_shape ι) {i j : ι} (h : i ≠ j) (A : V) :
  is_zero (((single V c j).obj A).X i) :=
begin
  change is_zero (ite (i = j) A 0),
  rw if_neg h,
  exact is_zero_zero V,
end

def _root_.homological_complex.single_obj_iso_zero (V : Type*) [_inst_1 : category V]
  [_inst_2 : has_zero_morphisms V] [_inst_3 : has_zero_object V] {ι : Type*}
  [_inst_4 : decidable_eq ι] (c : complex_shape ι) {i j : ι} (h : i ≠ j) (A : V) :
  ((single V c j).obj A).X i ≅ 0 :=
is_zero.iso_zero (homological_complex.single_obj_is_zero _ _ h _)

-- why does `homology_zero_zero` need a zero object?
-- move
lemma homology_is_zero_of_is_zero {V : Type*} [category V] [has_zero_morphisms V] {A B C : V}
  (hB : is_zero B) {f : A ⟶ B} {g : B ⟶ C} [has_kernels V] [has_images V] [has_cokernels V]
  [has_zero_object V]
  (w : f ≫ g = 0) : is_zero (homology f g w) :=
begin
  simp_rw is_zero.eq_zero_of_tgt hB f,
  simp_rw is_zero.eq_zero_of_src hB g,
  exact is_zero_of_iso_of_zero hB (homology_zero_zero.symm),
end

lemma single.d_eq_zero (V : Type*) [category V] [has_zero_morphisms V] [has_zero_object V]
  {ι : Type*} [decidable_eq ι] (c : complex_shape ι) (i j k : ι) ( v : V) :
  ((single V c i).obj v).d j k = 0 := rfl

lemma single.d_from_eq_zero (V : Type*) [category V] [has_zero_morphisms V] [has_zero_object V]
  {ι : Type*} [decidable_eq ι] (c : complex_shape ι) (i j : ι) ( v : V) :
  ((single V c i).obj v).d_from j = 0 :=
begin
  rcases hj : c.next j with _ | ⟨k, hjk⟩,
  { rw homological_complex.d_from_eq_zero _ hj, },
  { rw homological_complex.d_from_eq _ hjk,
    rw single.d_eq_zero,
    apply zero_comp,
  },
end

lemma single.d_to_eq_zero (V : Type*) [category V] [has_zero_morphisms V] [has_zero_object V]
  {ι : Type*} [decidable_eq ι] (c : complex_shape ι) (i j : ι) ( v : V) :
  ((single V c i).obj v).d_to j = 0 :=
begin
  rcases hj : c.prev j with _ | ⟨k, hjk⟩,
  { rw homological_complex.d_to_eq_zero _ hj, },
  { rw homological_complex.d_to_eq _ hjk,
    rw single.d_eq_zero,
    apply comp_zero,
  },
end

-- variant of homology_zero_zero
def homology_zero_zero' {V : Type*} [category V] [abelian V]
  {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (hf : f = 0) (hg : g = 0) :
  homology f g (by simp [hf]) ≅ B :=
(eq_to_iso (show homology f g _ = homology (0 : A ⟶ B) (0 : B ⟶ C) (by simp), by simp [hf, hg]))
  ≪≫ homology_zero_zero

lemma is_iso_cokernel_pi_image_to_kernel_of_zero_of_zero {V : Type*} [category V]
  [abelian V] {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (hf : f = 0) (hg : g = 0) :
is_iso (cokernel.π (image_to_kernel f g (by simp [hf]))) :=
begin
  subst hf,
  subst hg,
  rw image_to_kernel_zero_left,
  apply cokernel.π_of_zero,
end

lemma cokernel.desc_spec {V : Type*} [category V]
  [abelian V] {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
  (c : cokernel f ⟶ C) : (cokernel.π f ≫ c = g) ↔ c = cokernel.desc f g w :=
begin
  have h2 := cokernel.π_desc f g w,
  split,
  { rintro rfl,
    symmetry,
    rwa cancel_epi at h2, },
  { rintro rfl,
    assumption },
end

lemma cokernel.desc_comp_left {V : Type*} [category V]
  [abelian V] {A B C D : V} {f : A ⟶ B} {g : B ⟶ C} {e : C ⟶ D} (w : f ≫ g = 0) :
  (cokernel.desc f g w) ≫ e =
  (cokernel.desc f (g ≫ e) (by rw [← category.assoc, w, zero_comp])) :=
begin
  rw ← cokernel.desc_spec,
  simp [cokernel.π_desc],
end

lemma is_iso_cokernel.desc {V : Type*} [category V] [abelian V] {A B C : V} {f : A ⟶ B} {g : B ⟶ C}
  (h : exact f g) (h2 : epi g) : is_iso (cokernel.desc f g h.1) :=
is_iso_of_op (cokernel.desc f g h.w)

lemma sq_from_epi_of_epi {ι : Type*} {V : Type*} [_inst_1 : category V] [_inst_2 : abelian V]
  {c : complex_shape ι}
  {C₁ C₂ : homological_complex V c} [_inst_3 : has_zero_object V] (φ : C₁.hom C₂) (i : ι)
  (h2 : is_zero (C₂.X_next i)) [epi (φ.f i)] :
epi (homological_complex.hom.sq_from φ i) :=
⟨begin
  rintros ψ ⟨fL, fR, fw⟩ ⟨gL, gR, gw⟩,
  intro h,
  congr',
  { apply_fun category_theory.comma_morphism.left at h,
    simp at h,
    rwa cancel_epi at h, },
  { dsimp at fR gR,
    have fR0 : fR = 0 := is_zero.eq_zero_of_src h2 _,
    subst fR0,
    have gR0 : gR = 0 := is_zero.eq_zero_of_src h2 _,
    subst gR0, },
end⟩

@[simp] lemma epi_comp_iso_iff_epi {V : Type*} [category V] {A B C : V} (e : A ≅ B) (f : B ⟶ C) :
  epi (e.hom ≫ f) ↔ epi f :=
begin
  split,
  { rintro ⟨h⟩,
    constructor,
    intros Z s t h2,
    apply h,
    simp [h2], },
  { rintro ⟨h⟩,
    constructor,
    intros Z s t h2,
    apply h,
    simpa using h2,
  },
end

@[simp] lemma epi_iso_comp_iff_epi {V : Type*} [category V] {A B C : V} (f : A ⟶ B) (e : B ≅ C) :
  epi (f ≫ e.hom) ↔ epi f :=
begin
  split,
  { introI h,
    constructor,
    intros Z s t h2,
    suffices : e.inv ≫ s = e.inv ≫ t,
      simpa,
    rw ← cancel_epi (f ≫ e.hom),
    simpa using h2, },
  { introI h,
    constructor,
    intros Z s t h2,
    simp only [category.assoc] at h2,
    rw cancel_epi at h2,
    rwa cancel_epi at h2, },
end

lemma is_iso_iff_is_iso_comp_left {V : Type*} [category V] {A B C : V} (f : A ⟶ B) {e : B ⟶ C}
  [is_iso f] : is_iso (f ≫ e) ↔ is_iso e :=
begin
  split,
  { introI h, exact is_iso.of_is_iso_comp_left f e },
  { introI h, exact is_iso.comp_is_iso },
end

lemma is_iso_iff_is_iso_comp_right {V : Type*} [category V] {A B C : V} {f : A ⟶ B} (g : B ⟶ C)
  [is_iso g] : is_iso (f ≫ g) ↔ is_iso f :=
begin
  split,
  { introI, exact is_iso.of_is_iso_comp_right f g},
  { introI h, exact is_iso_of_op (f ≫ g), },
end
@[simp] lemma epi_comp_is_iso_iff_epi {V : Type*} [category V] {A B C : V} (e : A ⟶ B) (f : B ⟶ C)
  [is_iso e] : epi (e ≫ f) ↔ epi f :=
epi_comp_iso_iff_epi (as_iso e) f

@[simp] lemma epi_is_iso_comp_iff_epi {V : Type*} [category V] {A B C : V} (f : A ⟶ B) (e : B ⟶ C)
  [is_iso e] : epi (f ≫ e) ↔ epi f :=
epi_iso_comp_iff_epi f (as_iso e)

lemma kernel_subobject_map_epi_of_epi {C : Type*} [_inst_1 : category C] [abelian C] {X Y : C}
  {f : X ⟶ Y} (hY : is_zero Y)
   {X' Y' : C} {f' : X' ⟶ Y'} (hY' : is_zero Y')
    (φ : arrow.mk f ⟶ arrow.mk f') [epi φ.left] : epi (kernel_subobject_map φ) :=
begin
  have hf : f = 0 := is_zero.eq_zero_of_tgt hY _,
  have hf' : f' = 0 := is_zero.eq_zero_of_tgt hY' _,
  haveI hfiso : is_iso (kernel_subobject f).arrow,
  { rw [← kernel_subobject_arrow, hf],
    simp,
    apply_instance },
  haveI hf'iso : is_iso (kernel_subobject f').arrow,
  { rw [← kernel_subobject_arrow, hf'],
    simp,
    apply_instance },
  suffices : epi (kernel_subobject_map φ ≫ (kernel_subobject f').arrow),
  { rwa epi_is_iso_comp_iff_epi at this },
  rw kernel_subobject_map_arrow,
  simp,
  apply_instance,
end

lemma zero_of_epi_of_comp_zero {V : Type*} [category V] [abelian V]
  {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) [epi f] : g = 0 :=
(preadditive.epi_iff_cancel_zero f).mp infer_instance C g w

lemma epi_of_epi_of_comp_epi_of_mono {V : Type*} [category V] [abelian V]
  {A B C : V} (f : A ⟶ B) (g : B ⟶ C) [epi (f ≫ g)] [mono g] : epi f :=
begin
  haveI foo : is_iso g,
  { rw is_iso_iff_mono_and_epi,
    refine ⟨infer_instance, _⟩,
    apply epi_of_epi f,
  },
  simp * at *,
end

lemma image_to_kernel_epi_of_epi {V : Type*} [category V] [abelian V]
  {A B C : V} (f : A ⟶ B) (g : B ⟶ C) [epi f] (w : f ≫ g = 0) :
  epi (image_to_kernel f g w) :=
begin
  have claim0 := image_subobject_arrow_comp f,
  have claim : (image_subobject f).arrow = (image_to_kernel f g w) ≫ (kernel_subobject g).arrow,
  { exact (image_to_kernel_arrow f g w).symm},
  have claim2 := factor_thru_image_subobject_comp_image_to_kernel _ _ w,
  suffices : epi (factor_thru_kernel_subobject g f w),
  { rw ← claim2 at this,
    resetI,
    apply epi_of_epi (factor_thru_image_subobject f) (image_to_kernel f g w), },
  apply epi_of_epi_of_comp_epi_of_mono _ (kernel_subobject g).arrow,
  rw factor_thru_kernel_subobject_comp_arrow g f w,
  apply_instance,
end

lemma image_to_kernel_zero_left' {V : Type*} [category V] [has_zero_morphisms V]
  {A B C : V} {f : A ⟶ B} (hf : f = 0) (g : B ⟶ C) [has_kernels V]
  [has_zero_object V] [has_image f] :
image_to_kernel f g (by rw [hf, zero_comp]) = 0 :=
begin
  convert image_to_kernel_zero_left g,
  rw zero_comp,
end

lemma cokernel.desc_is_iso {A B C D : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (e : C ⟶ D) [is_iso e]
  (w : f ≫ g = 0) : cokernel.desc f g w ≫ e = cokernel.desc f (g ≫ e)
  (begin rw [← category.assoc, w, zero_comp] end) :=
begin
  rw ← cancel_epi (cokernel.π f),
  simp,
end

lemma image_to_kernel_eq_image_to_kernel_of_eq_snd {A B C : 𝓐} (f : A ⟶ B) {g h : B ⟶ C}
  (hgh : g = h) (w : f ≫ g = 0) : image_to_kernel f g w = image_to_kernel f h (by rw [← hgh, w]) ≫
  eq_to_hom (by rw hgh) :=
begin
  subst hgh,
  simp only [eq_to_hom_refl, category.comp_id],
end

lemma image_to_kernel_eq_image_to_kernel_of_eq_fst {A B C : 𝓐} (f g : A ⟶ B) {h : B ⟶ C}
  (hfg : f = g) (w : f ≫ h = 0) : image_to_kernel f h w = eq_to_hom (by rw hfg) ≫
    image_to_kernel g h (by rw [← hfg, w]) :=
begin
  subst hfg,
  simp only [eq_to_hom_refl, category.id_comp],
end

-- lemma cokernel.desc_with_isomorphisms {A B C D : 𝓐} (f : A ⟶ B) (e : B ⟶ C) (g : C ⟶ D)
--   [is_iso e] (w : f ≫ e ≫ g = 0) :
--   (cokernel_comp_is_iso f e).hom ≫ cokernel.desc f (e ≫ g) w =
--   cokernel.desc (f ≫ e) g (by simp [w]) :=
-- begin
--   simp,
--   admit, -- presumably this is true!
-- end


lemma homology_functor.is_iso_of_is_zero_of_is_zero_of_is_zero {ι : Type*} {c : complex_shape ι}
  {i j : ι} (hij : c.rel i j) {C₁ C₂ : homological_complex 𝓐 c} (h1from : C₁.d_from j = 0)
  (h2to : C₂.d_to j = 0) (h2from : C₂.d_from j = 0) (isomap : cokernel (C₁.d_to j) ≅ C₂.X j)
  {f : C₁ ⟶ C₂} (hf : f.f j = cokernel.π (C₁.d_to j) ≫ isomap.hom) :
is_iso ((homology_functor 𝓐 c j).map f) :=
begin
  rw [homology_functor_map],
  let h₁ : has_homology (C₁.d_to j) (C₁.d_from j) (cokernel (C₁.d_to j)) := has_homology.snd_eq_zero' h1from,
  let h₂ : has_homology (C₂.d_to j) (C₂.d_from j) (C₂.X j) := has_homology.fst_snd_eq_zero' h2to h2from,
  have := has_homology.map_iso_homology_map h₁ h₂
    (commsq.of_eq (homological_complex.hom.comm_to f j)).symm
    (commsq.of_eq (homological_complex.hom.comm_from f j)).symm,
  rw ← is_iso_iff_is_iso_comp_left ((h₁.iso (homology.has (C₁.d_to j) (C₁.d_from j) _)).hom),
  swap, apply_instance,
  rw ← is_iso_iff_is_iso_comp_right ((h₂.iso (homology.has (C₂.d_to j) (C₂.d_from j) _)).inv),
  swap, apply_instance,
  suffices h2 : is_iso (h₁.map h₂ (commsq.of_eq _).symm (commsq.of_eq _).symm),
  { rw this at h2, convert h2 using 1, simp, congr, },
  convert_to is_iso (isomap.hom), swap, apply_instance,
  simp [h₁, h₂, has_homology.map, has_homology.snd_eq_zero', has_homology.fst_snd_eq_zero', has_homology.desc, has_homology.lift, hf],
  symmetry,
  apply exact.epi_desc_unique,
  apply exact.mono_lift_unique,
  simp,
end

lemma map_is_iso (n : ℤ) : is_iso
  (homology.map (homological_complex.d_to_comp_d_from _ _)
    (homological_complex.d_to_comp_d_from _ _) (homological_complex.hom.sq_to (to_single C n) n)
    (homological_complex.hom.sq_from (to_single C n) n) rfl) :=
begin
/-
image_subobject (C.d_to) -> kernel_subobject (C.d_from) -> 0
 |
 \⧸
 0                       -> C.homology n                -> 0

-/
  change is_iso ((homology_functor 𝓐 (complex_shape.up ℤ) n).map (to_single C n)),
  refine homology_functor.is_iso_of_is_zero_of_is_zero_of_is_zero _ _ _ _ _ _,
  { exact (n-1)},
  { show _ = _, by ring},
  { rw d_from_eq_zero, linarith },
  { rw single.d_to_eq_zero, },
  { rw single.d_from_eq_zero, },
  { refine _ ≪≫ (homological_complex.single_obj_X_self _ _ _ _).symm,
    refine cokernel_iso_of_eq (homological_complex.d_to_eq (C.imker n) (show (n - 1) + 1 = n, by ring)) ≪≫ _,
    refine (cokernel_epi_comp _ _) ≪≫ _,
    refine cokernel_iso_of_eq (d_eq_im_to_ker _ rfl rfl) ≪≫ _,
    refine (cokernel_epi_comp _ _) ≪≫ _,
    apply cokernel_comp_is_iso, },
  { delta to_single,
    dsimp, simp, refl, },
end

instance to_single_quasi_iso (n : ℤ) :
  homotopy_category.is_quasi_iso $ (homotopy_category.quotient _ _).map (to_single C n) :=
⟨begin
  intro i,
  -- split into cases : the n'th map, and all the other maps,
  rcases eq_or_ne i n with (rfl | hin),
  { -- The n'th map is the nontrivial case.
    -- First there's this quotient map to the homotopy category which we replace by `homology_functor`.
    rw ← functor.comp_map,
    apply map_is_iso_of_iso_of_map_is_iso (homotopy_category.homology_factors 𝓐
      (complex_shape.up ℤ) i).symm,
      /- The goal now states that the middle arrow induces an isomorphism
         on homology of the below complexes:

         im d -> ker d -> 0
          |       |       |
          \/      \⧸      \/
           0  -> ker/im-> 0


      The main problem right now is that the homology of 0 -> ker/im -> 0 is in some sense
      quite far from ker/im, it's ker(ker/im->0)/im(0->ker/im).
      -/
    delta homology_functor, dsimp,
    apply map_is_iso, },
  { rcases eq_or_ne i (n-1) with (rfl | hin'),
    { rw ← functor.comp_map,
      apply map_is_iso_of_iso_of_map_is_iso (homotopy_category.homology_factors 𝓐
        (complex_shape.up ℤ) (n-1)).symm,
      apply is_iso_of_is_zero_of_is_zero,
      { delta homology_functor,
        dsimp,
        delta homological_complex.homology,
        delta homology,
        apply @is_zero_cokernel_of_epi _ _ _ _ _ _ _,
        have foo : homological_complex.d_to (C.imker n) (n - 1) = 0,
        { apply is_zero.eq_zero_of_src,
          have := homological_complex.X_prev_iso (C.imker n) (show (n-2)+1 = (n-1), by ring),
          apply is_zero_of_iso_of_zero _ this.symm,
          apply X_is_zero_of_ne;
          linarith },
        haveI : mono (homological_complex.d_from (C.imker n) (n - 1)),
        { rw homological_complex.d_from_eq (C.imker n) (show (n-1)+1=n, by ring),
          apply @mono_comp _ _ _ _ _ _ _,
          rw d_eq_im_to_ker _ rfl rfl,
          apply_instance, },
        convert image_to_kernel_epi_of_zero_of_mono (homological_complex.d_from (C.imker n) (n - 1)),
      },
      { rw ← functor.comp_obj,
        apply obj_is_zero_of_iso (homotopy_category.homology_factors 𝓐 (complex_shape.up ℤ) (n-1)).symm,
        rw homology_functor_obj,
        dsimp,
        apply homology_is_zero_of_is_zero,
        dsimp only,
        rw if_neg hin,
        apply is_zero_zero,
      }, },
    { apply is_iso_of_is_zero_of_is_zero,
      { rw ← functor.comp_obj,
        apply obj_is_zero_of_iso (homotopy_category.homology_factors 𝓐 (complex_shape.up ℤ) i).symm,
        rw homology_functor_obj,
        have hC := X_is_zero_of_ne C hin' hin,
        refine is_zero_of_iso_of_zero hC _,
        delta homological_complex.homology,
        symmetry,
        convert homology_zero_zero,
        apply is_zero.eq_zero_of_tgt hC,
        apply is_zero.eq_zero_of_src hC,
        all_goals {apply_instance},
      },
      { rw ← functor.comp_obj,
        apply obj_is_zero_of_iso (homotopy_category.homology_factors 𝓐 (complex_shape.up ℤ) i).symm,
        rw homology_functor_obj,
        apply homology_is_zero_of_is_zero,
        apply homological_complex.single_obj_is_zero _ _ hin,
      }
    }
  }
end⟩

end imker

end cochain_complex
