import category_theory.abelian.homology

noncomputable theory

universes v

open category_theory category_theory.limits opposite

variables {C : Type*} [category.{v} C] [abelian C]
variables {D : Type*} [category.{v} D] [abelian D]

variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)

variables (F : C ⥤ D) [functor.additive F]
variables [preserves_finite_limits F] [preserves_finite_colimits F]

include w

structure homology_iso_predatum :=
(K : C) (ι : K ⟶ Y) (f' : X ⟶ K) (fac : f' ≫ ι = f) (zero₁ : ι ≫ g = 0)
(H : C) (π : K ⟶ H) (zero₂ : f' ≫ π = 0)

omit w

namespace homology_iso_predatum

@[simps]
def tautological : homology_iso_predatum f g w :=
{ K := kernel g,
  ι := kernel.ι _,
  f' := kernel.lift g f w,
  fac := kernel.lift_ι _ _ _,
  zero₁ := kernel.condition _,
  H := cokernel (kernel.lift g f w),
  π := cokernel.π _,
  zero₂ := cokernel.condition _, }

@[simps]
def tautological' : homology_iso_predatum f g w :=
{ K := kernel g,
  ι := kernel.ι _,
  f' := kernel.lift g f w,
  fac := kernel.lift_ι _ _ _,
  zero₁ := kernel.condition _,
  H := homology f g w,
  π := homology.π' f g w,
  zero₂ := homology.condition_π' _ _ _, }

variables {f g w}

variable (h : homology_iso_predatum f g w)

@[simps]
def fork : kernel_fork g := kernel_fork.of_ι h.ι h.zero₁

@[simps]
def cofork : cokernel_cofork h.f' := cokernel_cofork.of_π h.π h.zero₂

@[simps]
def map {D : Type*} [category D] [abelian D] (F : C ⥤ D) [F.additive] :
  homology_iso_predatum (F.map f) (F.map g) (by rw [← F.map_comp, w, F.map_zero]) :=
{ K := F.obj h.K,
  ι := F.map h.ι,
  f' := F.map h.f',
  fac := by rw [← F.map_comp, h.fac],
  zero₁ := by rw [← F.map_comp, h.zero₁, F.map_zero],
  H := F.obj h.H,
  π := F.map h.π,
  zero₂ := by rw [← F.map_comp, h.zero₂, F.map_zero], }

end homology_iso_predatum

structure homology_iso_datum extends homology_iso_predatum f g w :=
(fork_is_limit : is_limit to_homology_iso_predatum.fork)
(cofork_is_colimit : is_colimit to_homology_iso_predatum.cofork)

namespace homology_iso_datum

@[simps]
def tautological : homology_iso_datum f g w :=
{ to_homology_iso_predatum := homology_iso_predatum.tautological f g w,
  fork_is_limit := by apply kernel_is_kernel,
  cofork_is_colimit := by apply cokernel_is_cokernel, }

@[simps]
def tautological' : homology_iso_datum f g w :=
{ to_homology_iso_predatum := homology_iso_predatum.tautological' f g w,
  fork_is_limit := by apply kernel_is_kernel,
  cofork_is_colimit := begin
    dsimp [homology_iso_predatum.cofork],
    refine is_colimit.of_iso_colimit (cokernel_is_cokernel (kernel.lift g f w)) _ ,
    refine cocones.ext (homology_iso_cokernel_lift f g w).symm _,
    rintro (_|_),
    tidy,
  end, }

variables {f g w}
variable (h : homology_iso_datum f g w)

@[simps]
def iso₁ : h.K ≅ kernel g :=
is_limit.cone_point_unique_up_to_iso h.fork_is_limit (limit_cone.is_limit _)

@[simps]
def iso₂ : h.H ≅ cokernel h.f' :=
is_colimit.cocone_point_unique_up_to_iso h.cofork_is_colimit (colimit_cocone.is_colimit _)

@[simps]
def iso : h.H ≅ homology f g w :=
begin
  refine h.iso₂ ≪≫ cokernel.map_iso _ _ (iso.refl _) h.iso₁ _ ≪≫
    (homology_iso_cokernel_lift f g w).symm,
  ext,
  simp only [iso₁_hom, equalizer_as_kernel, category.assoc, iso.refl_hom, category.id_comp,
    kernel.lift_ι, ← h.fac],
  congr' 1,
  apply kernel.lift_ι,
end

section map

def map :
  homology_iso_datum (F.map f) (F.map g) (by rw [← F.map_comp, w, F.map_zero]) :=
{ to_homology_iso_predatum := h.to_homology_iso_predatum.map F,
  fork_is_limit := begin
    let e : parallel_pair g 0 ⋙ F ≅ parallel_pair (F.map g) 0 :=
      parallel_pair.ext (iso.refl _) (iso.refl _) (by simp) (by simp),
    have hF := (is_limit.postcompose_inv_equiv e.symm _).inv_fun
      (is_limit_of_preserves F h.fork_is_limit),
    refine is_limit.of_iso_limit hF (cones.ext (iso.refl _) _),
    rintro (_|_),
    tidy,
  end,
  cofork_is_colimit := begin
    let e : parallel_pair h.f' 0 ⋙ F ≅ parallel_pair (F.map h.f') 0 :=
      parallel_pair.ext (iso.refl _) (iso.refl _) (by simp) (by simp),
    have hF := (is_colimit.precompose_inv_equiv e _).inv_fun
      (is_colimit_of_preserves F h.cofork_is_colimit),
    refine is_colimit.of_iso_colimit hF (cocones.ext (iso.refl _) _),
    rintro (_|_),
    tidy,
  end, }

end map

end homology_iso_datum

namespace category_theory

namespace functor

def homology_iso' : homology (F.map f) (F.map g) (by rw [← F.map_comp, w, F.map_zero]) ≅
    F.obj (homology f g w) :=
((homology_iso_datum.tautological' f g w).map F).iso.symm

end functor

end category_theory
