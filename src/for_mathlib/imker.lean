import algebra.homology.homological_complex
import algebra.homology.single
import category_theory.abelian.basic
import for_mathlib.split_exact
import for_mathlib.derived.defs

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
--lemma homology.map_factor_of_zero_of_zero {V : Type*} [category V] [abelian V] {A B C : V}
--   {f : A ⟶ B} {g : B ⟶ C} (hg : g = 0) {A' B' C' : V} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
--   (hf' : f' = 0) (α : arrow.mk f ⟶ arrow.mk f') (β : arrow.mk g ⟶ arrow.mk g')
--   (h : α.right = β.left) : homology.map (show f ≫ g = 0, by simp [hg]) (by simp [hf']) α β h = sorry := sorry

@[simps] def X_iso_image (n : ℤ) : (imker C n).X (n-1) ≅ image_subobject (C.d_to n) :=
eq_to_iso (by {rw [X_def, if_pos rfl]})

@[simps] def X_iso_image_of_eq {n i : ℤ} (h : i = n - 1) : (imker C n).X i ≅ image_subobject (C.d_to n) :=
eq_to_iso (by {rw [X_def, if_pos h]})

@[simps] def X_iso_kernel (n : ℤ) : (imker C n).X n ≅ kernel_subobject (C.d_from n) :=
eq_to_iso (by {rw [X_def, if_neg, if_pos rfl], linarith})

@[simps] def X_iso_kernel_of_eq {n i : ℤ} (h : i = n) : (imker C n).X i ≅ kernel_subobject (C.d_from n) :=
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

lemma d_interesting {n i j : ℤ} (h : i = n - 1) (hj : j = n) : (imker C n).d i j =
(X_iso_image_of_eq C h).hom ≫
image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n) ≫ (X_iso_kernel_of_eq _ hj).inv :=
begin
  simp only [h, hj, eq_self_iff_true, d_def, eq_to_iso.hom, dif_pos, X_iso_image_of_eq_hom,
    X_iso_kernel_of_eq_inv],
  refl,
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

/-- The natural map from `imker C n` to `H_n(C)[n]`. -/
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
     rw d_interesting C (show i = i + 1 - 1, by ring) rfl,
     simp only [category.assoc, iso.inv_hom_id_assoc, cokernel.condition_assoc, zero_comp,
       comp_zero], },
   { exact (hn rfl).elim },
   { rw comp_zero },
  end }
.

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
  (h : exact f g) (h2 : epi g) : is_iso
  (cokernel.desc f g h.1) :=
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
  -- I just made epi (iso ≫ f) ↔ epi f and epi (f ≫ iso) ↔ epi f
  -- but now I realise I need is_iso versions :-/
  suffices : epi (kernel_subobject_map φ ≫ (kernel_subobject f').arrow),
  { constructor,
    intros A g h h',
    suffices : inv ((kernel_subobject f').arrow) ≫ g = inv ((kernel_subobject f').arrow) ≫ h,
    { simpa },
    resetI,
    rw ← cancel_epi (kernel_subobject_map φ ≫ (kernel_subobject f').arrow),
    simp only [category.assoc, h', is_iso.hom_inv_id_assoc],
  },
  simp only [kernel_subobject_map_arrow],
  constructor,
  intros A g h h',
  simp only [category.assoc] at h',
  rw cancel_epi at h',
  rwa cancel_epi at h',
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

-- looks simple? kmb didn't find it so simple ;-)
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
    -- Adam says "do something else here"
    delta homology.map,
    dsimp only [homological_complex.d_to_comp_d_from, cokernel.condition, comp_zero, homological_complex.hom.sq_from_id,
      homology.π_map, kernel_subobject_map_id, category.id_comp, category.comp_id, homological_complex.hom.sq_from_comp,
      kernel_subobject_map_comp, category.assoc, homology.π_map_assoc],
    have foo : image_to_kernel (homological_complex.d_to (C.imker i) i) (homological_complex.d_from (C.imker i) i) _ ≫
      kernel_subobject_map (homological_complex.hom.sq_from (to_single C i) i) = 0,
    { rw [← cancel_epi (factor_thru_image_subobject (homological_complex.d_to (C.imker i) i)), comp_zero],
      rw [← cancel_mono ((kernel_subobject _).arrow)], swap, exact (kernel_subobject (((single 𝓐 (complex_shape.up ℤ) i).obj (homological_complex.homology C i)).d_from i)).arrow_mono,
      rw zero_comp,
      simp only [category.assoc, kernel_subobject_map_arrow, homological_complex.hom.sq_from_left, image_to_kernel_arrow_assoc,
        image_subobject_arrow_comp_assoc],
      rw homological_complex.d_to_eq,
      rw category.assoc,
      rw ← homological_complex.hom.comm,
      simp, swap, use i-1, show (i - 1) + 1 = i, ring,
    },
    rw ← cokernel.desc_comp_left foo,
    apply @is_iso.comp_is_iso _ _ _ _ _ _ _ _ _, swap,
    { apply is_iso_cokernel_pi_image_to_kernel_of_zero_of_zero,
      { apply single.d_to_eq_zero, },
      { apply single.d_from_eq_zero, },
    },
    apply is_iso_cokernel.desc, swap,
    { -- prove epi iff map in the middle epi because so many 0s
      --delta homological_complex.hom.sq_from arrow.hom_mk,
      --delta kernel_subobject_map subobject.factor_thru,
      --dsimp,
      -- This one shouldn't be too bad.
      apply kernel_subobject_map_epi_of_epi _ _ _,
      { have := homological_complex.X_next_iso (C.imker i) (show i + 1 = i + 1, by refl),
        apply is_zero_of_iso_of_zero _ this.symm,
        apply X_is_zero_of_ne;
        linarith, },
      { have := homological_complex.X_next_iso ((single 𝓐 (complex_shape.up ℤ) i).obj
          (homological_complex.homology C i)) (show i + 1 = i + 1, by refl),
        apply is_zero_of_iso_of_zero _ this.symm,
        delta single, dsimp, rw if_neg, apply is_zero_zero, linarith, },
      { delta homological_complex.hom.sq_from to_single to_single arrow.hom_mk,
        dsimp,
        rw dif_pos rfl,
        simp,
        exact strong_epi.epi, } },
    { refine ⟨foo, _⟩,
      /-
      C_{i-1}---(f)---> C_i ---(g)--> C_{i+1} (f and g both called d)

      It's a complex, so we get an induced map Im(f)->Ker(g).

      This map also forms part of a complex:

      im(f)->ker(g)->ker(ker(g)/im(f)->0) is a complex, so we get an induced map

      im(im(f)->ker(g)) -> ker(ker(g)->ker(ker(g)/im(f)->0))

      and the claim is that this is an epi.

      If
      A --(mono)-> B --(epi)-> C is a complex, then
      Im(d) -> Ker(d) is epi iff A -> ker(d) is an epi
      -/
      -- perhaps the next step is to show that ker(ker(g)->ker(ker(g)/im(f)->0) is iso to ker(g)?

      sorry }, },
  -- the below sorry can be removed, it's not even there. It's the proof that all the other
  -- vertical maps are isos on homology.
  sorry;{ rcases eq_or_ne i (n-1) with (rfl | hin'),
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
          rw d_interesting _ rfl rfl,
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
        apply homological_complex.single_obj_eq_zero _ _ hin,
      }
    }
  }
end⟩

end imker

end cochain_complex

--lemma homology.map_factor_of_zero_of_zero {V : Type*} [category V] [abelian V] {A B C : V}
--   {f : A ⟶ B} {g : B ⟶ C} (hg : g = 0) {A' B' C' : V} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
--   (hf' : f' = 0) (α : arrow.mk f ⟶ arrow.mk f') (β : arrow.mk g ⟶ arrow.mk g')
--   (h : α.right = β.left) : homology.map (show f ≫ g = 0, by simp [hg]) (by simp [hf']) α β h = sorry := sorry
