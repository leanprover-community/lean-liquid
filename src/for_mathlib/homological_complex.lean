import data.matrix.notation

import for_mathlib.snake_lemma2
import for_mathlib.short_exact_sequence

noncomputable theory

open category_theory
open category_theory.limits

universes v u

lemma preadditive.exact_of_iso_of_exact' {D : Type*} [category D] [abelian D]
  {A₁ B₁ C₁ A₂ B₂ C₂ : D}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
  (α : A₁ ≅ A₂) (β : B₁ ≅ B₂) (γ : C₁ ≅ C₂) (hsq₁ : α.hom ≫ f₂ = f₁ ≫ β.hom)
  (hsq₂ : β.hom ≫ g₂ = g₁ ≫ γ.hom)
  (h : exact f₁ g₁) :
  exact f₂ g₂ :=
preadditive.exact_of_iso_of_exact f₁ g₁ f₂ g₂ (arrow.iso_mk α β hsq₁) (arrow.iso_mk β γ hsq₂) rfl h

namespace homological_complex

variables {C : Type u} [category.{v} C] [abelian C]
variables {ι : Type*} {c : complex_shape ι}

def mod_boundaries (A : homological_complex C c) (j : ι) : C :=
cokernel ((A.boundaries j).arrow)

def mod_boundaries_map {A B : homological_complex C c} (f : A ⟶ B) (j : ι) :
  A.mod_boundaries j ⟶ B.mod_boundaries j :=
cokernel.map _ _ (boundaries_map f j) (f.f j) $ by { rw image_subobject_map_arrow, refl }

@[simps]
def mod_boundaries_functor (j : ι) : homological_complex C c ⥤ C :=
{ obj := λ A, A.mod_boundaries j,
  map := λ A B f, mod_boundaries_map f j,
  map_id' := λ A,
  begin
    delta mod_boundaries mod_boundaries_map cokernel.map, ext,
    show cokernel.π (A.boundaries j).arrow ≫ _ = cokernel.π (A.boundaries j).arrow ≫ _,
    simp only [cokernel.π_desc, category.id_comp, id_f, category.comp_id],
  end,
  map_comp' := λ X Y Z f g,
  begin
    delta mod_boundaries mod_boundaries_map cokernel.map, ext,
    show cokernel.π (X.boundaries j).arrow ≫ _ = cokernel.π (X.boundaries j).arrow ≫ _,
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc],
  end }
.

-- generalize to chain complexes over other shapes
@[simps]
def homology_to_mod_boundaries (n : ℕ) :
  homology_functor C (complex_shape.down ℕ) n ⟶ mod_boundaries_functor n :=
{ app := λ A, cokernel.map _ _ (𝟙 _) ((A.cycles n).arrow)
    (by simp only [boundaries_to_cycles_arrow, category.id_comp]),
  naturality' := λ A B f,
  begin
    ext,
    simp only [homology_functor_map, mod_boundaries_functor_map, homology.π_map_assoc],
    delta mod_boundaries_map homology.π cokernel.map cycles,
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc,
      kernel_subobject_map_arrow_assoc, hom.sq_from_left],
  end }
.

section

variables (A : chain_complex C ℕ) (n : ℕ)

def delta_to_boundaries : A.X (n+1) ⟶ (A.boundaries n) :=
(X_prev_iso A rfl).inv ≫ factor_thru_image_subobject _

instance delta_to_boundaries_epi : epi (delta_to_boundaries A n) :=
epi_comp _ _

@[ext] lemma boundaries.ext {X : C} (f g : (boundaries A n : C) ⟶ X)
  (h : delta_to_boundaries A n ≫ f = delta_to_boundaries A n ≫ g) : f = g :=
by rwa ← cancel_epi (delta_to_boundaries A n)

@[simp, reassoc] lemma delta_to_boundaries_comp_arrow :
  (delta_to_boundaries A n) ≫ (boundaries A n).arrow = A.d (n + 1) n :=
by rw [delta_to_boundaries, category.assoc, image_subobject_arrow_comp, X_prev_iso_comp_d_to]

@[simp, reassoc] lemma boundaries_arrow_comp_delta_to_boundaries :
  (boundaries _ _).arrow ≫ delta_to_boundaries A n = 0 :=
begin
  ext,
  simp only [delta_to_boundaries_comp_arrow_assoc, category.assoc, delta_to_boundaries_comp_arrow,
    d_comp_d, comp_zero, zero_comp],
end

def delta_to_cycles : A.X (n+1) ⟶ (A.cycles n) :=
delta_to_boundaries _ _ ≫ boundaries_to_cycles _ _

@[simp, reassoc] lemma delta_to_cycles_comp_arrow :
  (delta_to_cycles A n) ≫ (cycles A n).arrow = A.d (n + 1) n :=
by rw [delta_to_cycles, category.assoc, boundaries_to_cycles_arrow, delta_to_boundaries_comp_arrow]

@[simp, reassoc] lemma boundaries_arrow_comp_delta_to_cycles :
  (boundaries _ _).arrow ≫ delta_to_cycles A n = 0 :=
by rw [delta_to_cycles, ← category.assoc, boundaries_arrow_comp_delta_to_boundaries, zero_comp]

end

-- generalize to chain complexes over other shapes
@[simps]
def mod_boundaries_to_cycles (n : ℕ) :
  mod_boundaries_functor (n+1) ⟶ cycles_functor C (complex_shape.down ℕ) n :=
{ app := λ A, cokernel.desc _ (delta_to_cycles _ _) (boundaries_arrow_comp_delta_to_cycles _ _),
  naturality' := λ A B f,
  begin
    ext, show cokernel.π _ ≫ _ = cokernel.π _ ≫ _,
    simp only [homology_functor_map, mod_boundaries_functor_map, homology.π_map_assoc],
    delta mod_boundaries_map homology.π cokernel.map,
    simp only [category.assoc, cycles_functor_map, cycles_map_arrow, hom.comm,
      cokernel.π_desc_assoc, delta_to_cycles_comp_arrow_assoc, delta_to_cycles_comp_arrow]
  end }
.

-- generalize to chain complexes over other shapes
@[simps]
def cycles_to_homology (n : ℕ) :
  cycles_functor C (complex_shape.down ℕ) n ⟶ homology_functor C (complex_shape.down ℕ) n :=
{ app := λ A, cokernel.π _,
  naturality' := λ A B f,
  begin
    simp only [cycles_functor_map, homology_functor_map],
    delta homology.map,
    rw cokernel.π_desc, refl,
  end }

variables (C)

abbreviation Fst : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Fst C).map_homological_complex _

abbreviation Snd : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Snd C).map_homological_complex _

abbreviation Trd : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Trd C).map_homological_complex _

abbreviation Fst_Snd : Fst C ⟶ Snd C :=
nat_trans.map_homological_complex (short_exact_sequence.f_nat C) _

abbreviation Snd_Trd : Snd C ⟶ Trd C :=
nat_trans.map_homological_complex (short_exact_sequence.g_nat C) _

variables (A : chain_complex (short_exact_sequence C) ℕ)

def snake_diagram (n : ℕ) : chain_complex (short_exact_sequence C) ℕ → snake_diagram ⥤ C :=
snake_diagram.mk_functor''
  ![Fst C, Snd C, Trd C]
  ![homology_functor _ _ (n+1),
    mod_boundaries_functor (n+1),
    cycles_functor _ _ n,
    homology_functor _ _ n]
  (Fst_Snd C) (Snd_Trd C)
  (homology_to_mod_boundaries (n+1)) (mod_boundaries_to_cycles n) (cycles_to_homology n)

open_locale zero_object


instance Fst_Snd_mono (n : ℕ) : mono (((Fst_Snd C).app A).f n) := (A.X n).mono'

instance Snd_Trd_epi (n : ℕ) : epi (((Snd_Trd C).app A).f n) := (A.X n).epi'

instance Fst_Snd_Trd_exact (n : ℕ) : exact (((Fst_Snd C).app A).f n) (((Snd_Trd C).app A).f n) :=
(A.X n).exact'

instance uugh {A B : chain_complex C ℕ} (f : A ⟶ B) [∀ n, epi (f.f n)] (n : ℕ) :
  epi (f.prev n) :=
begin
  have : (complex_shape.down ℕ).rel (n+1) n := rfl,
  rw hom.prev_eq f this,
  apply_with epi_comp { instances := ff },
  { apply_instance },
  { apply epi_comp }
end

instance {A B : chain_complex C ℕ} (f : A ⟶ B) [∀ n, epi (f.f n)] (n : ℕ) :
  epi (boundaries_map f n) :=
begin
  let sq := hom.sq_to f n,
  haveI : epi sq.left := by { dsimp, apply_instance, },
  apply_with (epi_of_epi (factor_thru_image_subobject _)) { instances := ff },
  suffices : factor_thru_image_subobject (A.d_to n) ≫
      boundaries_map f n =
    sq.left ≫ factor_thru_image_subobject (B.d_to n),
  { rw this, apply epi_comp, },
  ext,
  simp only [category.assoc, image_subobject_map_arrow, hom.sq_to_right,
    image_subobject_arrow_comp_assoc, hom.sq_to_left, image_subobject_arrow_comp, hom.comm_to],
end

instance uuugher (A B : C) (f : A ⟶ B) : exact (kernel_subobject f).arrow f :=
by { rw [← kernel_subobject_arrow, exact_iso_comp], apply_instance }

instance uuugh (A : chain_complex C ℕ) (n : ℕ) : exact (cycles A n).arrow (d_from A n) :=
by delta cycles; apply_instance

lemma X_next_is_zero (A : chain_complex C ℕ) : is_zero (A.X_next 0) :=
begin
  apply is_zero_of_iso_of_zero (is_zero_zero _),
  apply (X_next_iso_zero A _).symm,
  delta complex_shape.next option.choice,
  simp only [dif_neg, complex_shape.down_rel, nat.succ_ne_zero, nonempty_subtype,
    exists_false, not_false_iff],
end

lemma next_eq_zero {A₁ A₂ : chain_complex C ℕ} (f : A₁ ⟶ A₂) :
  f.next 0 = 0 :=
(X_next_is_zero _ _).eq_zero_of_src _

instance jmc_is_weeping {A₁ A₂ : chain_complex C ℕ} (f : A₁ ⟶ A₂) (n : ℕ) [∀ n, mono (f.f n)] :
  mono (f.next n) :=
begin
  cases n,
  { refine ⟨λ Z a b H, _⟩, apply (X_next_is_zero _ _).eq_of_tgt },
  have : (complex_shape.down ℕ).rel n.succ n := rfl,
  rw hom.next_eq _ this,
  apply_with mono_comp { instances := ff },
  { apply_instance },
  { apply mono_comp }
end

instance jmc_is_crying {A₁ A₂ A₃ : chain_complex C ℕ} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (n : ℕ)
  [∀ n, exact (f.f n) (g.f n)] : exact (f.next n) (g.next n) :=
begin
  cases n,
  { rw [next_eq_zero],
    apply_with exact_zero_left_of_mono { instances := ff },
    { apply_instance },
    { refine ⟨λ Z a b H, _⟩, apply (X_next_is_zero _ _).eq_of_tgt } },
  have : (complex_shape.down ℕ).rel n.succ n := rfl,
  refine preadditive.exact_of_iso_of_exact' (f.f n) (g.f n) _ _
    (X_next_iso A₁ this).symm (X_next_iso A₂ this).symm (X_next_iso A₃ this).symm
    _ _ infer_instance;
  simp only [hom.next_eq _ this, iso.symm_hom, iso.inv_hom_id_assoc],
end

lemma exact_cycles_map_app {A₁ A₂ A₃ : chain_complex C ℕ} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (n : ℕ)
  [∀ n, exact (f.f n) (g.f n)] [epi (g.f n)] [∀ n, mono (f.f n)] :
  exact (cycles_map f n) (cycles_map g n) :=
begin
  have sq₁ :  d_from A₁ n ≫ f.next n = f.f n ≫ d_from A₂ n := (hom.comm_from _ _).symm,
  have sq₂ :  d_from A₂ n ≫ g.next n = g.f n ≫ d_from A₃ n := (hom.comm_from _ _).symm,
  suffices S : snake
    ↑(cycles A₁ n) ↑(cycles A₂ n) ↑(cycles A₃ n)
    (A₁.X n) (A₂.X n) (A₃.X n)
    _ _ _
    _ _ _
    (cycles_map f n) (cycles_map g n)
    (cycles _ n).arrow (cycles _ n).arrow (cycles _ n).arrow
    (f.f n) (g.f n)
    (A₁.d_from n) (A₂.d_from n) (A₃.d_from n)
    (f.next n) (g.next n)
    (cokernel.π $ A₁.d_from n) (cokernel.π $ A₂.d_from n) (cokernel.π $ A₃.d_from n)
    (cokernel.map _ _ _ _ sq₁) (cokernel.map _ _ _ _ sq₂),
  { exact S.six_term_exact_seq.pair },
  fsplit,
  { refine exact_seq.cons _ _ infer_instance _ ((exact_iff_exact_seq _ _).mp infer_instance) },
  { refine exact_seq.cons _ _ infer_instance _ ((exact_iff_exact_seq _ _).mp infer_instance) },
  { refine exact_seq.cons _ _ infer_instance _ ((exact_iff_exact_seq _ _).mp infer_instance) },
  { rw cycles_map_arrow, },
  { rw cycles_map_arrow, },
  { exact sq₁ },
  { exact sq₂ },
  { apply cokernel.π_desc, },
  { apply cokernel.π_desc, },
end

lemma mono_cycles_map_app (n : ℕ) : mono (cycles_map ((Fst_Snd C).app A) n) :=
begin
  apply_with (mono_of_mono _ (subobject.arrow _)) { instances := ff },
  rw cycles_map_arrow,
  haveI : mono (((Fst_Snd C).app A).f n) := (A.X n).mono',
  apply mono_comp,
end

@[simp] lemma image_subobject_arrow {X : C} (S : subobject X) :
  image_subobject (S.arrow) = S :=
begin
  delta image_subobject,
  ext,
  swap,
  { exact limits.image_mono_iso_source _ },
  { simp }
end

@[simp] lemma kernel_subobject_cokernel.π {X : C} (S : subobject X) :
  kernel_subobject (cokernel.π S.arrow) = S :=
begin
  delta kernel_subobject,
  ext,
  swap,
  { exact (abelian.image_iso_image _).trans (limits.image_mono_iso_source _) },
  { simp }
end

lemma exact.congr {X₁ X₂ Y Z₁ Z₂ : C} (f₁ : X₁ ⟶ Y) (g₁ : Y ⟶ Z₁) (f₂ : X₂ ⟶ Y) (g₂ : Y ⟶ Z₂)
  (h : exact f₁ g₁) (him : image_subobject f₁ = image_subobject f₂)
  (hker : kernel_subobject g₁ = kernel_subobject g₂) :
  exact f₂ g₂ :=
by rwa [abelian.exact_iff_image_eq_kernel, ← him, ← hker, ← abelian.exact_iff_image_eq_kernel]

lemma exact_column (A : chain_complex C ℕ) (n : ℕ) :
exact_seq C [(kernel.ι (A.d (n + 1) n)), (A.d (n + 1) n), (cokernel.π (A.boundaries n).arrow)] :=
begin
  refine exact_seq.cons _ _ exact_kernel_ι _ _,
  rw [← exact_iff_exact_seq],
  have : (complex_shape.down ℕ).rel (n + 1) n := rfl,
  refine exact.congr _ (boundaries A n).arrow _ _ _ infer_instance _ rfl,
  rw [← boundaries_eq_image_subobject A this, image_subobject_arrow]
end

lemma exact_mod_boundaries_map (n : ℕ) :
  exact (mod_boundaries_map ((Fst_Snd C).app A) n) (mod_boundaries_map ((Snd_Trd C).app A) n)
   :=
begin
  have sq1 : ((Fst C).obj A).d (n + 1) n ≫ (A.X n).f =
    (A.X (n+1)).f ≫ ((Snd C).obj A).d (n + 1) n,
  { simp [(A.d (n + 1) n).sq1] },
  have sq2 : ((Snd C).obj A).d (n + 1) n ≫ (A.X n).g =
    (A.X (n+1)).g ≫ ((Trd C).obj A).d (n + 1) n,
  { simp [(A.d (n + 1) n).sq2] },
  suffices S : snake
    (kernel _)                        (kernel _)                        (kernel _)
    (((Fst C).obj A).X (n+1))         (((Snd C).obj A).X (n+1))         (((Trd C).obj A).X (n+1))
    (((Fst C).obj A).X n)             (((Snd C).obj A).X n)             (((Trd C).obj A).X n)
    (mod_boundaries _ n)              (mod_boundaries _ n)              (mod_boundaries _ n)
    (kernel.map _ _ _ _ sq1)    (kernel.map _ _ _ _ sq2)
    (kernel.ι $ ((Fst C).obj A).d (n+1) n)
    (kernel.ι $ ((Snd C).obj A).d (n+1) n)
    (kernel.ι $ ((Trd C).obj A).d (n+1) n)
    (A.X (n+1)).f (A.X (n+1)).g
    (((Fst C).obj A).d (n+1) n) (((Snd C).obj A).d (n+1) n) (((Trd C).obj A).d (n+1) n)
    (A.X n).f (A.X n).g
    (cokernel.π _) (cokernel.π _) (cokernel.π _)
    (mod_boundaries_map ((Fst_Snd C).app A) n) (mod_boundaries_map ((Snd_Trd C).app A) n),
  { exact (S.six_term_exact_seq.drop 3).pair },
  fsplit,
  { apply exact_column },
  { apply exact_column },
  { apply exact_column },
  { simp },
  { simp },
  { exact sq1 },
  { exact sq2 },
  { simp [mod_boundaries_map] },
  { simp [mod_boundaries_map] }
end

lemma epi_mod_boundaries_map (n : ℕ) :
  epi (mod_boundaries_map ((Snd_Trd C).app A) n) :=
begin
  apply_with (epi_of_epi (cokernel.π _)) { instances := ff },
  haveI : epi (((Snd_Trd C).app A).f n) := (A.X n).epi',
  have : cokernel.π _ ≫ mod_boundaries_map ((Snd_Trd C).app A) n =
    ((Snd_Trd C).app A).f n ≫ cokernel.π _ := cokernel.π_desc _ _ _,
  rw this,
  apply epi_comp,
end

lemma mono_homology_to_mod_boundaries (A : chain_complex C ℕ) (n : ℕ) :
  mono ((homology_to_mod_boundaries n).app A) :=
cokernel.map_mono_of_epi_of_mono
  (boundaries A n) (cycles A n)
  (boundaries A n) (A.X n)
  _ _ _ _ _

variables {C}

@[simp] lemma image_subobject_comp_eq_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [epi f] :
  image_subobject (f ≫ g) = image_subobject g :=
begin
  delta image_subobject,
  haveI : is_iso (image.pre_comp f g) := is_iso_of_mono_of_epi _,
  ext, swap,
  { exact as_iso (image.pre_comp f g) },
  { simp only [as_iso_hom, image.pre_comp_ι], },
end

@[simp] lemma kernel_subobject_comp_eq_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [mono g] :
  kernel_subobject (f ≫ g) = kernel_subobject f :=
begin
  delta kernel_subobject,
  ext, swap,
  { exact kernel_comp_mono f g },
  { simp only [kernel_comp_mono_hom, kernel.lift_ι] },
end

lemma exact_cycles_arrow_delta_to_cycles (A : chain_complex C ℕ) (n : ℕ) :
  exact (A.cycles (n+1)).arrow (delta_to_cycles A n) :=
begin
  rw [category_theory.abelian.exact_iff_image_eq_kernel],
  dsimp [delta_to_cycles, delta_to_boundaries],
  simp only [image_subobject_arrow, kernel_subobject_comp_eq_of_mono],
  delta cycles,
  have : (complex_shape.down ℕ).rel (n + 1) n := rfl,
  let g : ↑(A.boundaries n) ⟶ X_next A (n + 1) := (A.boundaries n).arrow ≫ (X_next_iso _ this).inv,
  haveI : mono g := mono_comp _ _,
  suffices aux : delta_to_boundaries _ _ ≫ g = d_from A (n + 1),
  { simp_rw [← aux, kernel_subobject_comp_eq_of_mono], refl, },
  simp only [delta_to_boundaries_comp_arrow_assoc, iso.comp_inv_eq, d_from_comp_X_next_iso],
end

lemma exact_homology_to_mod_boundaries_to_cycles (A : chain_complex C ℕ) (n : ℕ) :
  exact ((homology_to_mod_boundaries (n+1)).app A) ((mod_boundaries_to_cycles n).app A) :=
begin
  let φ : homology A (n + 1) ⟶ mod_boundaries A (n + 1) :=
    limits.cokernel.desc _ ((kernel_subobject _).arrow ≫ (cokernel.π _)) (by simp),
  suffices S : snake
    (0:C) 0 0
    (A.boundaries (n+1)) (boundaries A (n+1)) 0
    (A.cycles (n+1)) (A.X (n+1)) (A.cycles n)
    (homology A (n+1)) (mod_boundaries A (n+1)) (A.cycles n)
    0 0
    0 0 0
    (𝟙 _) 0
    (boundaries_to_cycles _ _) (A.boundaries (n+1)).arrow 0
    (A.cycles (n+1)).arrow (delta_to_cycles _ _)
    (homology.π _ _ _) (cokernel.π _) (𝟙 _)
    φ ((mod_boundaries_to_cycles n).app A),
    { exact (S.six_term_exact_seq.drop 3).pair },
  letI : exact (cycles A (n + 1)).arrow (delta_to_cycles A n) :=
    exact_cycles_arrow_delta_to_cycles _ _,
  letI : epi (homology.π (d_to A (n + 1)) (d_from A (n + 1)) _) := coequalizer.π_epi,
  fsplit,
  { refine exact_seq.cons _ _ (category_theory.exact_zero_mono _) _ _,
    rw [← exact_iff_exact_seq],
    exact abelian.exact_cokernel _ },
  { refine exact_seq.cons _ _ (category_theory.exact_zero_mono _) _ _,
    rw [← exact_iff_exact_seq],
    apply_instance },
  { refine exact_seq.cons _ _ (category_theory.exact_zero_mono _) _ _,
    rw [← exact_iff_exact_seq],
    apply_instance },
  { simp },
  { simp },
  { simp },
  { simp [boundaries_arrow_comp_delta_to_cycles] },
  { dsimp [homology.π, cycles],
    simp },
  { simp },
end

lemma exact_mod_boundaries_to_cycles_to_homology (A : chain_complex C ℕ) (n : ℕ) :
  exact ((mod_boundaries_to_cycles n).app A) ((cycles_to_homology n).app A)  :=
begin
  refine exact.congr _ (boundaries_to_cycles _ _) _ _ _ _ _ rfl,
  { simp only [cycles_to_homology_app],
    delta boundaries_to_cycles,
    apply_instance },
  { simp only [mod_boundaries_to_cycles_app],
    delta delta_to_cycles,
    rw [← image_subobject_comp_eq_of_epi (cokernel.π _)],
    simp only [cokernel.π_desc, image_subobject_comp_eq_of_epi], }
end

lemma epi_cycles_to_homology (A : chain_complex C ℕ) (n : ℕ) :
  epi ((cycles_to_homology n).app A) :=
coequalizer.π_epi

lemma snake_diagram_is_snake_input (n : ℕ) : is_snake_input (snake_diagram C n A) :=
{ row_exact₁ := begin
    dsimp [snake_diagram, snake_diagram.mk_functor'', snake_diagram.mk_functor'],
    simp only [snake_diagram.mk_functor_map_f1, snake_diagram.mk_functor_map_g1],
    exact exact_mod_boundaries_map _ _ _,
  end,
  row_exact₂ := begin
    dsimp [snake_diagram, snake_diagram.mk_functor'', snake_diagram.mk_functor'],
    simp only [snake_diagram.mk_functor_map_f2, snake_diagram.mk_functor_map_g2],
    exact exact_cycles_map_app _ _ _ n,
  end,
  col_exact₁ := begin
    intro j,
    dsimp [snake_diagram, snake_diagram.mk_functor'', snake_diagram.mk_functor'],
    fin_cases j with [0, 1, 2];
    simp only [snake_diagram.mk_functor_map_a0, snake_diagram.mk_functor_map_a1,
      snake_diagram.mk_functor_map_b0, snake_diagram.mk_functor_map_b1,
      snake_diagram.mk_functor_map_c0, snake_diagram.mk_functor_map_c1];
    exact exact_homology_to_mod_boundaries_to_cycles _ _,
  end,
  col_exact₂ := begin
    intro j,
    dsimp [snake_diagram, snake_diagram.mk_functor'', snake_diagram.mk_functor'],
    fin_cases j with [0, 1, 2];
    simp only [snake_diagram.mk_functor_map_a1, snake_diagram.mk_functor_map_a2,
      snake_diagram.mk_functor_map_b1, snake_diagram.mk_functor_map_b2,
      snake_diagram.mk_functor_map_c1, snake_diagram.mk_functor_map_c2];
    exact exact_mod_boundaries_to_cycles_to_homology _ _,
  end,
  col_mono := begin
    intro j,
    dsimp [snake_diagram, snake_diagram.mk_functor'', snake_diagram.mk_functor'],
    fin_cases j with [0, 1, 2];
    simp only [snake_diagram.mk_functor_map_a0, snake_diagram.mk_functor_map_b0,
      snake_diagram.mk_functor_map_c0];
    exact mono_homology_to_mod_boundaries _ _ _,
  end,
  col_epi := begin
    intro j,
    dsimp [snake_diagram, snake_diagram.mk_functor'', snake_diagram.mk_functor'],
    fin_cases j with [0, 1, 2];
    simp only [snake_diagram.mk_functor_map_a2, snake_diagram.mk_functor_map_b2,
      snake_diagram.mk_functor_map_c2];
    exact epi_cycles_to_homology _ _,
  end,
  row_mono := begin
    dsimp [snake_diagram, snake_diagram.mk_functor'', snake_diagram.mk_functor'],
    simp only [snake_diagram.mk_functor_map_f2],
    exact mono_cycles_map_app _ _ _
  end,
  row_epi := begin
    dsimp [snake_diagram, snake_diagram.mk_functor'', snake_diagram.mk_functor'],
    simp only [snake_diagram.mk_functor_map_g1],
    exact epi_mod_boundaries_map _ _ _
  end }

def snake_input {C : Type*} [category C] [abelian C] (n : ℕ) :
  chain_complex (short_exact_sequence C) ℕ → snake_input C :=
λ A, ⟨snake_diagram C n A, snake_diagram_is_snake_input A n⟩

def δ {C : Type*} [category C] [abelian C] (n : ℕ) (A : chain_complex (short_exact_sequence C) ℕ) :
  homology ((Trd C).obj A) (n+1) ⟶ homology ((Fst C).obj A) n :=
(snake_input n A).2.δ

lemma six_term_exact_seq {C : Type*} [category C] [abelian C]
  (n : ℕ) (A : chain_complex (short_exact_sequence C) ℕ) :
  exact_seq C [
    (homology_functor _ _ (n+1)).map ((Fst_Snd C).app A), -- Hⁿ⁺¹(A₁) ⟶ Hⁿ⁺¹(A₂)
    (homology_functor _ _ (n+1)).map ((Snd_Trd C).app A), -- Hⁿ⁺¹(A₂) ⟶ Hⁿ⁺¹(A₃)
    δ n A,                                                -- Hⁿ⁺¹(A₃) ⟶  Hⁿ(A₁)
    (homology_functor _ _ n).map ((Fst_Snd C).app A),     --  Hⁿ(A₁)  ⟶  Hⁿ(A₂)
    (homology_functor _ _ n).map ((Snd_Trd C).app A)      --  Hⁿ(A₁)  ⟶  Hⁿ(A₃)
  ] :=
begin
  have key := (snake_input n A).2.six_term_exact_seq,
  dsimp only [snake_input, snake_diagram,
    snake_diagram.mk_functor'', snake_diagram.mk_functor'] at key,
  refine exact_seq.congr key _, clear key,
  iterate 5 { refine exact_seq.arrow_congr.cons _ _, rotate },
  { apply exact_seq.arrow_congr.nil },
  { apply snake_diagram.mk_functor_map_f0 },
  { apply snake_diagram.mk_functor_map_g0 },
  { refl },
  { apply snake_diagram.mk_functor_map_f3 },
  { apply snake_diagram.mk_functor_map_g3 },
end

end homological_complex
