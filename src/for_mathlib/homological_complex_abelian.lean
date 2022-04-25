import algebra.homology.additive
import category_theory.abelian.basic
import category_theory.limits.constructions.epi_mono

open category_theory category_theory.limits

namespace homological_complex

universes w' w v v' u u'

variables {V : Type u} [category.{v} V] {J : Type w} [category.{w'} J]
variables {ι : Type u'} {c : complex_shape ι}

--move this
lemma congr_f [has_zero_morphisms V] {X Y : homological_complex V c} {f g : X ⟶ Y}
  (h : f = g) (x : ι) : f.f x = g.f x := congr_arg _ h

section limits

noncomputable theory

variables [has_zero_morphisms V] (F : J ⥤ homological_complex V c)

include F

@[simps]
def lift_of_is_limit_eval (t : cone F) (h : ∀ i, is_limit $ (eval V c i).map_cone t) (s : cone F) :
  s.X ⟶ t.X :=
begin
  refine ⟨λ i, is_limit.lift (h i) ⟨_, _⟩, _⟩,
  refine ⟨λ x, (s.π.app x).f i, _⟩,
  { intros x y f, dsimp, rw [category.id_comp, ← comp_f], congr, exact (cone.w s f).symm },
  { intros i j r,
    apply (h j).hom_ext,
    intro x,
    dsimp,
    rw [category.assoc, category.assoc],
    erw [← (t.π.app x).comm, (h j).fac _ x, (h i).fac_assoc _ x, (s.π.app x).comm],
    refl }
end
.
/-- `eval` jointly reflects (actually creates) limits -/
def is_limit_of_is_limit_eval (t : cone F) (h : ∀ i, is_limit $ (eval V c i).map_cone t) :
  is_limit t :=
{ lift := lift_of_is_limit_eval F t h,
  fac' := by { intros s j, ext, dsimp, exact (h x).fac _ j },
  uniq' := by { intros s m w, ext, apply (h x).hom_ext,
    intro j, dsimp, erw (h x).fac _ j, exact congr_f (w j) x } }

variables [∀ i : ι, has_limit (F ⋙ eval V c i)]

@[simps]
def limit_complex : homological_complex V c :=
begin
  refine ⟨λ i, limit (F ⋙ eval V c i), λ i j, limit.lift _ ⟨_, _⟩, _, _⟩,
  refine ⟨λ k, limit.π (F ⋙ eval V c i) k ≫ (F.obj k).d i j, _⟩,
  { intros x y f,
    dsimp,
    rw [category.id_comp, category.assoc, ← hom.comm, ← category.assoc],
    congr' 1,
    exact (limit.w _ _).symm },
  { intros i j r,
    ext k,
    rw [limit.lift_π, zero_comp],
    dsimp only,
    rw [(F.obj k).shape _ _ r, comp_zero] },
  { intros i j k r r', ext, simp }
end
.
@[simps]
def limit_complex_cone : cone F :=
{ X := limit_complex F,
  π := { app := λ x, { f := λ i, limit.π (F ⋙ eval V c i) x },
    naturality' := λ X Y f, by { ext, dsimp, rw category.id_comp, exact (limit.w _ _).symm } } }
.
def limit_complex_cone_is_limit : is_limit (limit_complex_cone F) :=
is_limit_of_is_limit_eval _ _
begin
  intro i,
  apply (limit.is_limit _).of_iso_limit,
  exact cones.ext (iso.refl _) (λ _, (category.id_comp _).symm),
end

def eval_map_limit_complex_cone (i : ι) :
  (eval V c i).map_cone (limit_complex_cone F) ≅ (get_limit_cone (F ⋙ eval V c i)).1 :=
cones.ext (iso.refl _) (λ j, by { dsimp, simpa })

instance (i : ι) : preserves_limit F (eval V c i) :=
preserves_limit_of_preserves_limit_cone (limit_complex_cone_is_limit F)
  ((limit.is_limit _).of_iso_limit (eval_map_limit_complex_cone F i).symm)

instance : has_limit F :=
⟨⟨⟨_, limit_complex_cone_is_limit F⟩⟩⟩

omit F

instance [has_limits_of_shape J V] : has_limits_of_shape J (homological_complex V c) := {}
instance [has_limits_of_size.{w' w} V] : has_limits_of_size.{w' w} (homological_complex V c) := ⟨⟩
instance [has_limits_of_shape J V] (i : ι) : preserves_limits_of_shape J (eval V c i) := {}
instance [has_limits_of_size.{w' w} V] (i : ι) : preserves_limits_of_size.{w' w} (eval V c i) := {}

end limits

section colimits

noncomputable theory

variables [has_zero_morphisms V] (F : J ⥤ homological_complex V c)

include F

@[simps]
def desc_of_is_colimit_eval (t : cocone F) (h : ∀ i, is_colimit $ (eval V c i).map_cocone t)
  (s : cocone F) :
  t.X ⟶ s.X :=
begin
  refine ⟨λ i, is_colimit.desc (h i) ⟨_, _⟩, _⟩,
  refine ⟨λ x, (s.ι.app x).f i, _⟩,
  { intros x y f, dsimp, rw [category.comp_id, ← comp_f], congr, exact cocone.w s f },
  { intros i j r,
    apply (h i).hom_ext,
    intro x,
    dsimp,
    erw [(t.ι.app x).comm_assoc, (h j).fac _ x, (h i).fac_assoc _ x, (s.ι.app x).comm] }
end
.
/-- `eval` jointly reflects (actually creates) colimits -/
def is_colimit_of_is_colimit_eval (t : cocone F) (h : ∀ i, is_colimit $ (eval V c i).map_cocone t) :
  is_colimit t :=
{ desc := desc_of_is_colimit_eval F t h,
  fac' := by { intros s j, ext, dsimp, exact (h x).fac _ j },
  uniq' := by { intros s m w, ext, apply (h x).hom_ext,
    intro j, dsimp, erw (h x).fac _ j, exact congr_f (w j) x } }

variable [∀ i : ι, has_colimit (F ⋙ eval V c i)]

@[simps]
def colimit_complex : homological_complex V c :=
begin
  refine ⟨λ i, colimit (F ⋙ eval V c i), λ i j, colimit.desc _ ⟨_, _⟩, _, _⟩,
  refine ⟨λ x, (F.obj x).d i j ≫ colimit.ι (F ⋙ eval V c j) x, _⟩,
  { intros x y f,
    dsimp,
    rw [category.comp_id, hom.comm_assoc],
    congr' 1,
    exact colimit.w (F ⋙ eval V c j) _ },
  { intros i j r,
    ext x,
    rw [colimit.ι_desc, comp_zero],
    dsimp only,
    rw [(F.obj x).shape _ _ r, zero_comp] },
  { intros i j k r r', ext, simp }
end
.
@[simps]
def colimit_complex_cocone : cocone F :=
{ X := colimit_complex F,
  ι := { app := λ x, { f := λ i, colimit.ι (F ⋙ eval V c i) x },
    naturality' := λ X Y f,
      by { ext, dsimp, rw category.comp_id, exact colimit.w (F ⋙ eval V c x) _ } } }
.

def colimit_complex_cocone_is_colimit : is_colimit (colimit_complex_cocone F) :=
is_colimit_of_is_colimit_eval _ _
begin
  intro i,
  apply (colimit.is_colimit _).of_iso_colimit,
  exact cocones.ext (iso.refl _) (λ _, category.comp_id _),
end
.

def eval_map_colimit_complex_cocone (i : ι) :
  (eval V c i).map_cocone (colimit_complex_cocone F) ≅ (get_colimit_cocone (F ⋙ eval V c i)).1 :=
cocones.ext (iso.refl _) (λ j, by { dsimp, simpa })

instance (i : ι) : preserves_colimit F (eval V c i) :=
preserves_colimit_of_preserves_colimit_cocone (colimit_complex_cocone_is_colimit F)
  ((colimit.is_colimit _).of_iso_colimit (eval_map_colimit_complex_cocone F i).symm)

instance : has_colimit F :=
⟨⟨⟨_, colimit_complex_cocone_is_colimit F⟩⟩⟩

omit F

instance [has_colimits_of_shape J V] : has_colimits_of_shape J (homological_complex V c) := {}
instance [has_colimits_of_size.{w' w} V] : has_colimits_of_size.{w' w} (homological_complex V c) :=
{}

instance [has_colimits_of_shape J V] (i : ι) : preserves_colimits_of_shape J (eval V c i) := {}
instance [has_colimits_of_size.{w' w} V] (i : ι) :
  preserves_colimits_of_size.{w' w} (eval V c i) := {}

end colimits


section biproduct

variables [has_zero_morphisms V] [has_binary_biproducts V] {X Y Z : homological_complex V c}

@[simps]
def biproduct (X Y : homological_complex V c) : homological_complex V c :=
{ X := λ i, X.X i ⊞ Y.X i,
  d := λ i j, biprod.map (X.d i j) (Y.d i j),
  shape' := λ i j r, by ext; simp [X.shape _ _ r, Y.shape _ _ r] }
.
@[simps] def biproduct.inl : X ⟶ biproduct X Y := { f := λ i, biprod.inl }
@[simps] def biproduct.inr : Y ⟶ biproduct X Y := { f := λ i, biprod.inr }
@[simps] def biproduct.fst : biproduct X Y ⟶ X := { f := λ i, biprod.fst }
@[simps] def biproduct.snd : biproduct X Y ⟶ Y := { f := λ i, biprod.snd }
@[simps] def biproduct.lift (f : X ⟶ Y) (g : X ⟶ Z) : X ⟶ biproduct Y Z :=
{ f := λ i, biprod.lift (f.f i) (g.f i) }
@[simps] def biproduct.desc (f : X ⟶ Z) (g : Y ⟶ Z) : biproduct X Y ⟶ Z :=
{ f := λ i, biprod.desc (f.f i) (g.f i) }
.
variables (X Y)
@[simps]
def biproduct_bicone : binary_bicone X Y :=
{ X := biproduct X Y,
  fst := biproduct.fst,
  snd := biproduct.snd,
  inl := biproduct.inl,
  inr := biproduct.inr }
.
local attribute [tidy] tactic.case_bash

def biproduct_bicone_is_prod : is_limit (biproduct_bicone X Y).to_cone :=
{ lift := λ (Z : binary_fan _ _), biproduct.lift Z.fst Z.snd,
  uniq' := by { intros, delta binary_fan.fst binary_fan.snd, ext; simp [← w] } }
.
def biproduct_bicone_is_coprod : is_colimit (biproduct_bicone X Y).to_cocone :=
{ desc := λ (Z : binary_cofan _ _), biproduct.desc Z.inl Z.inr,
  uniq' := by { intros, delta binary_cofan.inl binary_cofan.inr, ext; simp [← w] } }
.
def biproduct_is_biprod : binary_biproduct_data X Y :=
{ bicone := biproduct_bicone X Y,
  is_bilimit := ⟨biproduct_bicone_is_prod X Y, biproduct_bicone_is_coprod X Y⟩ }

instance : has_binary_biproducts (homological_complex V c) :=
⟨λ X Y, ⟨⟨biproduct_is_biprod X Y⟩⟩⟩

end biproduct

instance [has_zero_morphisms V] [has_finite_products V] :
  has_finite_products (homological_complex V c) := ⟨λ J _ _, by exactI infer_instance⟩

-- instance [has_zero_morphisms V] [has_kernels V] : has_kernels (homological_complex V c) :=
-- begin
--   constructor,
--   intros X Y f,
--   apply_with homological_complex.category_theory.limits.has_limit { instances := ff },
--   intro i,
--   let : walking_parallel_pair_op_equiv.{v v}.functor ⋙ walking_parallel_pair_op_equiv.inverse ⋙
--     parallel_pair f 0 ⋙ eval V c i ≅ parallel_pair (f.f i) 0 :=
--     nat_iso.of_components (λ i, eq_to_iso $ by cases i; refl)
--       (by { rintros _ _ (_|_|_); dsimp; simp }),
--   have := has_limit_of_iso this.symm,
--   exact @@has_limit_of_equivalence_comp _ _ _
--     (walking_parallel_pair_op_equiv.{v v}.trans walking_parallel_pair_op_equiv.symm) this
-- end

-- instance [has_zero_morphisms V] [has_cokernels V] :
--   has_cokernels (homological_complex V c) :=
-- begin
--   constructor,
--   intros X Y f,
--   apply_with homological_complex.category_theory.limits.has_colimit { instances := ff },
--   intro i,
--   let : walking_parallel_pair_op_equiv.{v v}.functor ⋙ walking_parallel_pair_op_equiv.inverse ⋙
--     parallel_pair f 0 ⋙ eval V c i ≅ parallel_pair (f.f i) 0 :=
--     nat_iso.of_components (λ i, eq_to_iso $ by cases i; refl)
--       (by { rintros _ _ (_|_|_); dsimp; simp }),
--   have := has_colimit_of_iso this,
--   exact @@has_colimit_of_equivalence_comp _ _ _
--     (walking_parallel_pair_op_equiv.{v v}.trans walking_parallel_pair_op_equiv.symm) this
-- end

section kernel

variables [has_zero_morphisms V] {X Y : homological_complex V c}
variables (f : X ⟶ Y) [∀ i, has_kernel (f.f i)]

@[simps]
def kernel_complex : homological_complex V c :=
{ X := λ i, kernel (f.f i),
  d := λ i j, kernel.map _ _ _ _ (f.comm i j),
  shape' := by { introv r, ext, simp [X.shape _ _ r] } }
.
@[simps]
def kernel_complex_ι : kernel_complex f ⟶ X :=
{ f := λ i, kernel.ι (f.f i) }
.
@[simps]
def kernel_complex_fork : kernel_fork f :=
kernel_fork.of_ι (kernel_complex_ι f) (by { ext, simp })
.
@[simps]
def kernel_complex_lift (s : kernel_fork f) : s.X ⟶ kernel_complex f :=
{ f := λ i, kernel.lift _ (s.ι.f i)
    (by { rw [← comp_f, kernel_fork.condition], refl }) }

def kernel_complex_is_kernel : is_limit (kernel_complex_fork f) :=
begin
  apply is_limit_aux (kernel_complex_fork f) (kernel_complex_lift f),
  { intro s, ext, delta fork.ι, dsimp, simp only [kernel.lift_ι] },
  { intros s m h, ext, apply_fun (λ f, hom.f f x) at h,
    delta fork.ι at h, dsimp at h ⊢, simp [h, kernel.lift_ι] }
end
.
instance : has_kernel f := ⟨⟨⟨_, kernel_complex_is_kernel f⟩⟩⟩
instance [has_kernels V] : has_kernels (homological_complex V c) := {}
.
end kernel

section cokernel

variables [has_zero_morphisms V] {X Y : homological_complex V c}
variables (f : X ⟶ Y) [∀ i, has_cokernel (f.f i)]

@[simps]
def cokernel_complex : homological_complex V c :=
{ X := λ i, cokernel (f.f i),
  d := λ i j, cokernel.map _ _ _ _ (f.comm i j),
  shape' := by { introv r, ext, simp [Y.shape _ _ r] } }
.
@[simps]
def cokernel_complex_π : Y ⟶ cokernel_complex f :=
{ f := λ i, cokernel.π (f.f i) }
.
@[simps]
def cokernel_complex_cofork : cokernel_cofork f :=
cokernel_cofork.of_π (cokernel_complex_π f) (by { ext, simp })
.
@[simps]
def cokernel_complex_desc (s : cokernel_cofork f) : cokernel_complex f ⟶ s.X :=
{ f := λ i, cokernel.desc _ (s.π.f i)
    (by { rw [← comp_f, cokernel_cofork.condition], refl }) }

def cokernel_complex_is_cokernel : is_colimit (cokernel_complex_cofork f) :=
begin
  apply is_colimit_aux (cokernel_complex_cofork f) (cokernel_complex_desc f),
  { intro s, ext, delta cofork.π, dsimp, simp only [cokernel.π_desc] },
  { intros s m h, ext, apply_fun (λ f, hom.f f x) at h,
    delta cofork.π at h, dsimp at h ⊢, simp only [h, cokernel.π_desc] }
end
.
instance : has_cokernel f := ⟨⟨⟨_, cokernel_complex_is_cokernel f⟩⟩⟩
instance [has_cokernels V] : has_cokernels (homological_complex V c) := {}
.
end cokernel

section normal_mono

variables [abelian V] {X Y Z : homological_complex V c}
variables (f : X ⟶ Y)

def is_kernel_of_eval (g : Y ⟶ Z) (w : f ≫ g = 0)
  (h : ∀ i, is_limit (kernel_fork.of_ι (f.f i) (congr_f w i))) :
  is_limit (kernel_fork.of_ι f w) :=
begin
  refine is_limit.of_iso_limit (kernel_complex_is_kernel g) _,
  fapply cones.ext,
  fapply hom.iso_of_components,
  intro i, exact limit.iso_limit_cone ⟨_, h i⟩,
  { intros i j r, dsimp, rw [← iso.comp_inv_eq, category.assoc, ← iso.eq_inv_comp], ext, simp },
  { rintro (_|_),
    { ext, dsimp, rw ← iso.inv_comp_eq, simp },
    { ext, dsimp, simp [(show f.f x ≫ g.f x = _, from congr_f w x)] } }
end

def is_cokernel_of_eval (g : Y ⟶ Z) (w : f ≫ g = 0)
  (h : ∀ i, is_colimit (cokernel_cofork.of_π (g.f i) (congr_f w i))) :
  is_colimit (cokernel_cofork.of_π g w) :=
begin
  refine is_colimit.of_iso_colimit (cokernel_complex_is_cokernel f) _,
  fapply cocones.ext,
  fapply hom.iso_of_components,
  intro i, exact colimit.iso_colimit_cocone ⟨_, h i⟩,
  { intros i j r, ext, dsimp, simp },
  { rintro (_|_),
    { ext, dsimp, simpa using (congr_arg (λ f, hom.f f x) w).symm },
    { ext, dsimp, simp } }
end
.

-- move this
lemma has_pullback_of_size (C : Type u) [category.{v} C] [has_pullbacks C] :
  has_limits_of_shape walking_cospan.{w} C :=
has_limits_of_shape_of_equivalence walking_cospan_equiv.{v}

-- move this
lemma has_pushout_of_size (C : Type u) [category.{v} C] [has_pushouts C] :
  has_colimits_of_shape walking_span.{w} C :=
has_colimits_of_shape_of_equivalence walking_span_equiv.{v}

instance [mono f] (i : ι) : mono (f.f i) :=
begin
  change mono ((eval V c i).map f),
  haveI := has_pullback_of_size.{max u' v} V,
  exact category_theory.preserves_mono _ f,
end

lemma mono_of_eval [∀ i, mono (f.f i)] : mono f :=
begin
  constructor,
  intros Z g h r,
  ext i,
  rw ← cancel_mono (f.f i),
  exact congr_f r i
end

lemma mono_iff_eval : mono f ↔ ∀ i, mono (f.f i) :=
⟨λ _ i, by exactI infer_instance, λ _, by exactI mono_of_eval f⟩

instance [epi f] (i : ι) : epi (f.f i) :=
begin
  change epi ((eval V c i).map f),
  haveI := has_pushout_of_size.{max u' v} V,
  exact category_theory.preserves_epi _ f,
end

lemma epi_of_eval [∀ i, epi (f.f i)] : epi f :=
begin
  constructor,
  intros Z g h r,
  ext i,
  rw ← cancel_epi (f.f i),
  exact congr_f r i
end

lemma epi_iff_eval : epi f ↔ ∀ i, epi (f.f i) :=
⟨λ _ i, by exactI infer_instance, λ _, by exactI epi_of_eval f⟩

def normal_mono [mono f] : normal_mono f :=
{ Z := cokernel_complex f,
  g := cokernel_complex_π f,
  w := by { ext, simp },
  is_limit :=
  begin
    apply is_kernel_of_eval,
    intro i,
    exact abelian.mono_is_kernel_of_cokernel _ (colimit.is_colimit _)
  end }

def normal_epi [epi f] : normal_epi f :=
{ W := kernel_complex f,
  g := kernel_complex_ι f,
  w := by { ext, simp },
  is_colimit :=
  begin
    apply is_cokernel_of_eval,
    intro i,
    exact abelian.epi_is_cokernel_of_kernel _ (limit.is_limit _)
  end }
.

end normal_mono

instance [abelian V] : abelian (homological_complex V c) :=
{ normal_mono_of_mono := λ _ _, normal_mono,
  normal_epi_of_epi := λ _ _, normal_epi }

end homological_complex
