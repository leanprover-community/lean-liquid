import category_theory.abelian.homology
import algebra.homology.homology
import for_mathlib.has_homology

noncomputable theory

universes v

open category_theory category_theory.limits opposite

variables {C : Type*} [category.{v} C] [abelian C]
variables {D : Type*} [category.{v} D] [abelian D]

variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (H : C) (w : f ≫ g = 0)

variables (F : C ⥤ D) [functor.additive F]

/-- This structure expresses that there is a candidate `H` for the
homology of composable maps `f : X ⟶ Y` and `g : Y ⟶ Z`.
When `0 ⟶ K ⟶ Y ⟶ Z` and `X ⟶ K ⟶ Q ⟶ 0` are exact, this
will give a `h : homology_iso_datum f g H` and there shall
be an isomorphism `h.iso : H ≅ homology f g h.w`. The differences with
`has_homology f g H` are :
* this definition is not self dual: the homology is thought as the
quotient of cycles by boundaries;
* the object `K` can be any choice for the kernel of `Y ⟶ Z` and
`H` can be any choice of cokernel for `X ⟶ K`. -/
@[nolint has_inhabited_instance]
structure homology_iso_predatum :=
(w : f ≫ g = 0)
(K : C) (ι : K ⟶ Y) (f' : X ⟶ K) (fac' : f' ≫ ι = f) (zero₁' : ι ≫ g = 0)
(π : K ⟶ H) (zero₂' : f' ≫ π = 0)

namespace homology_iso_predatum

restate_axiom fac'
restate_axiom zero₁'
restate_axiom zero₂'
attribute [simp, reassoc] fac zero₁ zero₂

@[simps]
def tautological : homology_iso_predatum f g (cokernel (kernel.lift g f w)) :=
{ w := w,
  K := kernel g,
  ι := kernel.ι _,
  f' := kernel.lift g f w,
  fac' := kernel.lift_ι _ _ _,
  zero₁' := kernel.condition _,
  π := cokernel.π _,
  zero₂' := cokernel.condition _, }

@[simps]
def tautological' : homology_iso_predatum f g (homology f g w):=
{ w := w,
  K := kernel g,
  ι := kernel.ι _,
  f' := kernel.lift g f w,
  fac' := kernel.lift_ι _ _ _,
  zero₁' := kernel.condition _,
  π := homology.π' f g w,
  zero₂' := homology.condition_π' _ _ _, }

variables {f g}

variables {H} (h : homology_iso_predatum f g H)

@[simps]
def fork : kernel_fork g := kernel_fork.of_ι h.ι h.zero₁

@[simps]
def cofork : cokernel_cofork h.f' := cokernel_cofork.of_π h.π h.zero₂

@[simps]
def apply_functor {D : Type*} [category D] [abelian D] (F : C ⥤ D) [F.additive] :
  homology_iso_predatum (F.map f) (F.map g) (F.obj H):=
{ w := by rw [← F.map_comp, h.w, F.map_zero],
  K := F.obj h.K,
  ι := F.map h.ι,
  f' := F.map h.f',
  fac' := by rw [← F.map_comp, h.fac],
  zero₁' := by simp only [← F.map_comp, zero₁, F.map_zero],
  π := F.map h.π,
  zero₂' := by simp only [← F.map_comp, zero₂, F.map_zero], }

include h

@[simps]
def map_iso {X' Y' Z' : C} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (e₁ : arrow.mk f ≅ arrow.mk f')
  (e₂ : arrow.mk g ≅ arrow.mk g') (eq : e₁.hom.right = e₂.hom.left) :
  homology_iso_predatum f' g' H :=
begin
  have comm₁ : e₁.hom.left ≫ f' = f ≫ e₁.hom.right := arrow.w e₁.hom,
  have comm₂ : e₂.hom.left ≫ g' = g ≫ e₂.hom.right := arrow.w e₂.hom,
  have h₁ : e₁.inv.left ≫ e₁.hom.left = 𝟙 X',
  { rw [← comma.comp_left, e₁.inv_hom_id, arrow.id_left], refl, },
  exact
  { w := by { rw [← cancel_epi e₁.hom.left, ← category.assoc, comm₁, eq, category.assoc, comm₂,
      ← category.assoc, h.w, zero_comp, comp_zero], },
    K := h.K,
    ι := h.ι ≫ e₁.hom.right,
    f' := e₁.inv.left ≫ h.f',
    fac' := begin
      slice_lhs 2 3 { rw h.fac', },
      rw [← comm₁, ← category.assoc, h₁, category.id_comp],
    end,
    zero₁' := by rw [eq, category.assoc, comm₂, ← category.assoc, h.zero₁', zero_comp],
    π := h.π,
    zero₂' := by rw [category.assoc, h.zero₂', comp_zero], }
end

omit h

end homology_iso_predatum

@[nolint has_inhabited_instance]
structure homology_iso_datum (H : C) extends homology_iso_predatum f g H :=
(fork_is_limit : is_limit to_homology_iso_predatum.fork)
(cofork_is_colimit : is_colimit to_homology_iso_predatum.cofork)

namespace homology_iso_datum

variable {H}

@[simps]
def tautological : homology_iso_datum f g (cokernel (kernel.lift g f w)) :=
{ to_homology_iso_predatum := homology_iso_predatum.tautological f g w,
  fork_is_limit := by apply kernel_is_kernel,
  cofork_is_colimit := by apply cokernel_is_cokernel, }

@[simps]
def tautological' : homology_iso_datum f g (homology f g w) :=
{ to_homology_iso_predatum := homology_iso_predatum.tautological' f g w,
  fork_is_limit := by apply kernel_is_kernel,
  cofork_is_colimit := begin
    dsimp [homology_iso_predatum.cofork],
    refine is_colimit.of_iso_colimit (cokernel_is_cokernel (kernel.lift g f w)) _ ,
    refine cocones.ext (homology_iso_cokernel_lift f g w).symm _,
    rintro (_|_),
    tidy,
  end, }

variables {f g} (h : homology_iso_datum f g H)

def map_iso {X' Y' Z' : C} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (e₁ : arrow.mk f ≅ arrow.mk f')
  (e₂ : arrow.mk g ≅ arrow.mk g') (eq : e₁.hom.right = e₂.hom.left) :
  homology_iso_datum f' g' H :=
{ to_homology_iso_predatum := h.to_homology_iso_predatum.map_iso f' g' e₁ e₂ eq,
  fork_is_limit := begin
    refine (is_limit.equiv_of_nat_iso_of_iso _ _ _ _).to_fun h.fork_is_limit,
    { refine parallel_pair.ext (arrow.right_func.map_iso e₁) (arrow.right_func.map_iso e₂)
       _ (by simp),
      have h₂ := arrow.w e₂.hom,
      dsimp at h₂ ⊢,
      rw [eq, h₂], },
    { refine cones.ext (iso.refl _) _,
      rintro (_|_),
      tidy, },
  end,
  cofork_is_colimit := begin
    refine (is_colimit.equiv_of_nat_iso_of_iso _ _ _ _).to_fun h.cofork_is_colimit,
    { refine parallel_pair.ext ((arrow.left_func.map_iso e₁)) (iso.refl _) _ (by tidy),
      { dsimp,
        have h₁ : e₁.hom.left ≫ e₁.inv.left = 𝟙 X,
        { rw [← comma.comp_left, e₁.hom_inv_id, arrow.id_left], refl, },
        rw [category.comp_id, ← category.assoc, h₁, category.id_comp], }, },
    { refine cocones.ext (iso.refl _) _,
      rintro (_|_),
      tidy, },
  end, }

def iso₁ : h.K ≅ kernel g :=
is_limit.cone_point_unique_up_to_iso h.fork_is_limit (limit_cone.is_limit _)

@[simp, reassoc]
lemma iso₁_hom_kernel_ι : h.iso₁.hom ≫ kernel.ι g = h.ι :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ _

instance : mono h.ι := by { rw ← h.iso₁_hom_kernel_ι, apply_instance, }

@[simp, reassoc]
lemma f'_iso₁_hom : h.f' ≫ h.iso₁.hom = kernel.lift g f h.w :=
begin
  ext,
  simp only [category.assoc, iso₁_hom_kernel_ι, homology_iso_predatum.fac, kernel.lift_ι],
end

def iso₂ : H ≅ cokernel h.f' :=
is_colimit.cocone_point_unique_up_to_iso h.cofork_is_colimit (colimit_cocone.is_colimit _)

@[simp, reassoc]
lemma cokernel_π_iso₂_inv : cokernel.π h.f' ≫ h.iso₂.inv = h.π :=
is_colimit.comp_cocone_point_unique_up_to_iso_inv _ _ _

instance : epi h.π := by { rw ← h.cokernel_π_iso₂_inv, apply epi_comp, }

def iso₃ : cokernel h.f' ≅ cokernel (kernel.lift g f h.w) :=
cokernel.map_iso _ _ (iso.refl _) h.iso₁
  (by simp only [f'_iso₁_hom, iso.refl_hom, category.id_comp])

@[simp, reassoc]
lemma cokernel_π_iso₃_hom :
  cokernel.π h.f' ≫ h.iso₃.hom = h.iso₁.hom ≫ cokernel.π (kernel.lift g f h.w) :=
begin
  dsimp only [iso₃],
  simp only [cokernel.map_iso_hom, cokernel.π_desc],
end

variables (f g)

@[simp]
lemma tautological_iso₁ : (tautological f g w).iso₁ = iso.refl _ :=
begin
  ext,
  dsimp only [iso₁],
  simp only [equalizer_as_kernel, iso.refl_hom, category.id_comp],
  change kernel.lift _ _ _ ≫ _ = _,
  simpa only [equalizer_as_kernel, kernel.lift_ι],
end

@[simp]
lemma tautological'_iso₁ : (tautological' f g w).iso₁ = iso.refl _ :=
begin
  ext,
  dsimp only [iso₁],
  simp only [equalizer_as_kernel, iso.refl_hom, category.id_comp],
  change kernel.lift _ _ _ ≫ _ = _,
  simpa only [equalizer_as_kernel, kernel.lift_ι],
end

@[simp]
lemma tautological_iso₂ : (tautological f g w).iso₂ = iso.refl _ :=
begin
  suffices : (tautological f g w).iso₂.symm = iso.refl _,
  { change (tautological f g w).iso₂.symm.symm = _,
    simpa only [this], },
  ext,
  simpa only [iso.symm_hom, cokernel_π_iso₂_inv, iso.refl_hom, category.comp_id],
end

@[simp]
lemma tautological_iso₃ : (tautological f g w).iso₃ = iso.refl _ :=
begin
  ext,
  simpa only [cokernel_π_iso₃_hom, tautological_iso₁, iso.refl_hom, category.id_comp, category.comp_id],
end

variables {f g}

def iso : H ≅ homology f g h.w :=
h.iso₂ ≪≫ h.iso₃ ≪≫ (homology_iso_cokernel_lift f g h.w).symm

variables (f g)

@[simp]
lemma tautological_iso : (tautological f g w).iso =
  (homology_iso_cokernel_lift f g w).symm :=
by { dsimp only [iso], simp only [tautological_iso₂, tautological_iso₃, iso.refl_trans], }

lemma tautological_iso_hom : (tautological f g w).iso.hom =
  (homology_iso_cokernel_lift f g w).inv :=
by simp only [tautological_iso, iso.symm_hom]

variables {f g}

@[nolint has_inhabited_instance]
structure change {H₁ H₂ : C} (h₁ : homology_iso_datum f g H₁)
  (h₂ : homology_iso_datum f g H₂) :=
(κ : h₁.K ⟶ h₂.K) (fac₁' : h₁.f' ≫ κ = h₂.f') (fac₂' : κ ≫ h₂.ι = h₁.ι)
(η : H₁ ⟶ H₂) (fac₃' : h₁.π ≫ η = κ ≫ h₂.π)

namespace change

restate_axiom fac₁'
restate_axiom fac₂'
restate_axiom fac₃'
attribute [simp, reassoc] fac₁ fac₂
attribute [reassoc] fac₃

variables {H₁ H₂ : C} {h₁ : homology_iso_datum f g H₁}
  {h₂ : homology_iso_datum f g H₂} (c : change h₁ h₂)

@[simp, reassoc]
lemma fac_iso₁ : c.κ ≫ h₂.iso₁.hom = h₁.iso₁.hom :=
by { ext, simp only [category.assoc, iso₁_hom_kernel_ι, fac₂], }

instance : is_iso c.κ := is_iso.of_is_iso_fac_right (c.fac_iso₁)

def coker_iso : cokernel h₁.f' ≅ cokernel h₂.f' :=
cokernel.map_iso _ _ (iso.refl _) (as_iso c.κ)
(by simp only [as_iso_hom, fac₁, iso.refl_hom, category.id_comp])

@[simp, reassoc]
lemma coker_iso_comm : cokernel.π h₁.f' ≫ c.coker_iso.hom = c.κ ≫ cokernel.π h₂.f' :=
begin
  dsimp only [coker_iso],
  simp only [as_iso_hom, cokernel.map_iso_hom, cokernel.π_desc],
end

@[reassoc]
lemma fac_iso₂ : c.coker_iso.hom ≫ h₂.iso₂.inv = h₁.iso₂.inv ≫ c.η :=
begin
  ext,
  simp only [coker_iso_comm_assoc, cokernel_π_iso₂_inv, cokernel_π_iso₂_inv_assoc,
    fac₃],
end

instance : is_iso c.η :=
begin
  haveI : is_iso (h₁.iso₂.inv ≫ c.η) := by { rw ← fac_iso₂, apply_instance, },
  apply is_iso.of_is_iso_comp_left (h₁.iso₂.inv),
end

@[simp, reassoc]
lemma coker_iso_iso₃_hom : c.coker_iso.hom ≫ h₂.iso₃.hom = h₁.iso₃.hom :=
begin
  ext,
  simp only [coker_iso_comm_assoc, cokernel_π_iso₃_hom, fac_iso₁_assoc],
end

@[simp, reassoc]
lemma η_iso₂_hom_iso₃_hom : c.η ≫ h₂.iso₂.hom ≫ h₂.iso₃.hom = h₁.iso₂.hom ≫ h₁.iso₃.hom :=
by rw [← cancel_epi h₁.iso₂.inv, iso.inv_hom_id_assoc, ← c.coker_iso_iso₃_hom,
  ← fac_iso₂_assoc, iso.inv_hom_id_assoc]

@[simp, reassoc]
lemma η_iso_hom : c.η ≫ h₂.iso.hom = h₁.iso.hom :=
begin
  dsimp only [iso],
  simp only [iso.trans_hom, η_iso₂_hom_iso₃_hom_assoc],
end

lemma η_iso : as_iso c.η ≪≫ h₂.iso = h₁.iso :=
by { ext, simp only [iso.trans_hom, as_iso_hom, η_iso_hom], }

variables (f g)

@[simps]
def tautological : change (homology_iso_datum.tautological' f g w)
  (homology_iso_datum.tautological f g w) :=
{ κ := 𝟙 _,
  η := (homology_iso_cokernel_lift f g w).hom,
  fac₁' := category.comp_id _,
  fac₂' := category.id_comp _,
  fac₃' := begin
    dsimp [homology.π', homology_iso_cokernel_lift, homology_iso_cokernel_image_to_kernel'],
    simp only [cokernel_iso_of_eq_inv_comp_desc, cokernel.π_desc_assoc, category.assoc,
      π_comp_cokernel_iso_of_eq_hom, iso.inv_hom_id_assoc, category.id_comp],
  end, }

end change

variables (f g)

lemma tautological'_iso : (tautological' f g w).iso = iso.refl _ :=
begin
  ext1,
  rw ← (change.tautological f g w).η_iso_hom,
  simp only [← (change.tautological f g w).η_iso_hom, change.tautological_η,
    iso.refl_hom, tautological_iso, iso.symm_hom, iso.hom_inv_id],
end

variables {f g}

section apply_exact_functor

variables [preserves_finite_limits F] [preserves_finite_colimits F]

def apply_exact_functor : homology_iso_datum (F.map f) (F.map g) (F.obj H) :=
{ to_homology_iso_predatum := h.to_homology_iso_predatum.apply_functor F,
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

end apply_exact_functor

section homological_complex

variables {A : Type*} [category A] [abelian A]
variables {M : Type*} {c : complex_shape M}

def of_homological_complex (X : homological_complex A c) (i j k : M)
  (hij : c.rel i j) (hjk : c.rel j k) :
  homology_iso_datum (X.d i j) (X.d j k) (X.homology j) :=
begin
  refine (homology_iso_datum.tautological' (X.d_to j) (X.d_from j)
    (X.d_to_comp_d_from j)).map_iso _ _ _ _ _,
  { refine arrow.iso_mk (X.X_prev_iso hij) (iso.refl _) _,
    dsimp,
    simp only [X.d_to_eq hij, category.comp_id], },
  { refine arrow.iso_mk (iso.refl _) (X.X_next_iso hjk) _,
    dsimp,
    simp only [X.d_from_eq hjk, category.id_comp, category.assoc, iso.inv_hom_id,
      category.comp_id], },
  { refl, },
end

open_locale zero_object

def of_homological_complex_of_next_eq_none (X : homological_complex A c) (i j : M)
  (hij : c.rel i j) (hj : c.next j = none) :
  homology_iso_datum (X.d i j) (0 : _ ⟶ 0) (X.homology j) :=
begin
  refine (homology_iso_datum.tautological' (X.d_to j) (X.d_from j)
    (X.d_to_comp_d_from j)).map_iso _ _ _ _ _,
  { refine arrow.iso_mk (X.X_prev_iso hij) (iso.refl _) _,
    dsimp,
    simp only [X.d_to_eq hij, category.comp_id], },
  { refine arrow.iso_mk (iso.refl _) (X.X_next_iso_zero hj) _,
    simp only [arrow.mk_hom, comp_zero, homological_complex.d_from_comp_X_next_iso_zero], },
  { refl, },
end

end homological_complex

section has_homology

variables (f g)

lemma homology_iso_cokernel_lift_comp_ι :
  (homology_iso_cokernel_lift f g w).inv ≫ homology.ι f g w =
  cokernel.map _ _ (𝟙 X) (kernel.ι g) (by simp only [kernel.lift_ι, category.id_comp]) :=
begin
  ext,
  dsimp [homology_iso_cokernel_lift, homology.ι,
    homology_iso_cokernel_image_to_kernel', homology_iso_kernel_desc],
  simp only [cokernel_iso_of_eq_inv_comp_desc, category.assoc, cokernel.π_desc_assoc, cokernel.π_desc,
    cokernel_iso_of_eq_hom_comp_desc_assoc, kernel.lift_ι, kernel_subobject_arrow_assoc,
    kernel_subobject_arrow'_assoc],
end

lemma homology_ι_eq :
  homology.ι f g w = (homology_iso_cokernel_lift f g w).hom ≫
    cokernel.map _ _ (𝟙 X) (kernel.ι g) (by simp only [kernel.lift_ι, category.id_comp]) :=
by simp only [← homology_iso_cokernel_lift_comp_ι, iso.hom_inv_id_assoc]

variables {f g}

lemma iso_hom_homology_ι_eq_iso₂_hom_cokernel_map :
  h.iso.hom ≫ homology.ι f g h.w = h.iso₂.hom ≫ cokernel.map h.f' f (𝟙 X) h.ι (by simp) :=
begin
  dsimp only [iso, iso₂, iso₃],
  simp only [homology_ι_eq f g h.w, iso.refl_hom, iso.trans_hom, cokernel.map_iso_hom,
    iso.symm_hom, category.assoc, iso.inv_hom_id_assoc, iso.cancel_iso_hom_left],
  ext,
  simp only [cokernel.π_desc_assoc, category.assoc, cokernel.π_desc, iso₁_hom_kernel_ι_assoc],
end

lemma homology_π'_eq :
  homology.π' f g h.w = h.iso₁.inv ≫ h.π ≫ h.iso.hom :=
begin
  rw ← cancel_mono (homology.ι f g h.w),
  dsimp only [iso],
  simp only [homology.π'_ι, category.assoc, iso.trans_hom, iso.symm_hom,
    homology_iso_cokernel_lift_comp_ι, ← cokernel_π_iso₂_inv, iso.inv_hom_id_assoc,
    cokernel_π_iso₃_hom_assoc, cokernel.π_desc],
end

def has_homology : has_homology f g H :=
{ w := h.w,
  π := h.iso₁.inv ≫ h.π,
  ι := h.iso₂.hom ≫ cokernel.map h.f' f (𝟙 X) h.ι (by simp),
  π_ι := by simp only [category.assoc, ← cokernel_π_iso₂_inv_assoc, iso.inv_hom_id_assoc,
      cokernel.π_desc, ← h.iso₁_hom_kernel_ι],
  ex_π := begin
    refine preadditive.exact_of_iso_of_exact (kernel.lift g f h.w)
      (cokernel.π (kernel.lift g f h.w)) _ _ (iso.refl _) _ _ (abelian.exact_cokernel _),
    { refine arrow.iso_mk (iso.refl _) (h.iso₃.symm ≪≫ h.iso₂.symm) _,
      dsimp,
      simp only [← cancel_mono h.iso₂.hom, ← cancel_mono h.iso₃.hom,
        category.id_comp, category.assoc, ← cokernel_π_iso₂_inv,
        iso.inv_hom_id_assoc, cokernel_π_iso₃_hom,
        iso.inv_hom_id, category.comp_id], },
    { refl, },
  end,
  ι_ex := begin
    refine preadditive.exact_of_iso_of_exact (homology.ι f g h.w) (cokernel.desc f g h.w)
      _ _ _ (iso.refl _) _ (homology.has f g h.w).ι_ex,
    { refine arrow.iso_mk h.iso.symm (iso.refl _) _,
      dsimp,
      simp only [← h.iso_hom_homology_ι_eq_iso₂_hom_cokernel_map,
        iso.inv_hom_id_assoc, category.comp_id], },
    { refl, },
  end,
  epi_π := epi_comp _ _,
  mono_ι := begin
    rw ← iso_hom_homology_ι_eq_iso₂_hom_cokernel_map,
    apply_instance,
  end, }

end has_homology

end homology_iso_datum
