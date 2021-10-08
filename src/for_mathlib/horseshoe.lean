import for_mathlib.projectives
import for_mathlib.homological_complex

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace short_exact_sequence

variables {C : Type u} [category.{v} C] [abelian C] [enough_projectives C]

-- move this
lemma exact_of_epi_comp_kernel.ι_comp_mono {C : Type u} [category.{v} C] [abelian C] {X Y Z W : C}
  (g : Y ⟶ Z) (h : Z ⟶ W) (f : X ⟶ kernel g) (i : kernel g ⟶ Y) (hf : epi f) (hh : mono h)
  (hi : i = kernel.ι g) : exact (f ≫ i) (g ≫ h) :=
begin
  suffices : exact i g,
  { letI := hf,
    letI := hh,
    letI := this,
    letI : exact (f ≫ i) g := exact_epi_comp,
    exact exact_comp_mono },
  rw [hi],
  exact exact_kernel_ι
end

-- move this
def biprod_factors (A B : C) [projective A] [projective B]
  (E X : C) (f : A ⊞ B ⟶ X) (e : E ⟶ X) [epi e] :
  ∃ f' : A ⊞ B ⟶ E, f' ≫ e = f :=
⟨biprod.desc
  (projective.factor_thru (biprod.inl ≫ f) e)
  (projective.factor_thru (biprod.inr ≫ f) e),
  by ext; simp only [projective.factor_thru_comp, biprod.inl_desc_assoc, biprod.inr_desc_assoc]⟩

variables (A B : short_exact_sequence C) (f : A ⟶ B)

def horseshoe_base : short_exact_sequence C :=
short_exact_sequence.mk_split (projective.over A.1) (projective.over A.3)

def horseshoe_base_π : horseshoe_base A ⟶ A :=
{ fst := projective.π _,
  snd := biprod.desc (projective.π _ ≫ A.f) (projective.factor_thru (projective.π _) A.g),
  trd := projective.π _,
  sq1' := by { dsimp [horseshoe_base], simp only [biprod.inl_desc], },
  sq2' :=
  begin
    dsimp [horseshoe_base], apply category_theory.limits.biprod.hom_ext',
    { simp only [zero_comp, exact.w_assoc, biprod.inl_desc_assoc, category.assoc,
        short_exact_sequence.f_comp_g, comp_zero], },
    { simp only [projective.factor_thru_comp, biprod.inr_snd_assoc, biprod.inr_desc_assoc], }
  end }

instance epi_horseshoe_base_π_1 : epi (horseshoe_base_π A).1 :=
show epi (projective.π _), by apply_instance

instance epi_horseshoe_base_π_2 : epi (horseshoe_base_π A).2 := sorry

instance epi_horseshoe_base_π_3 : epi (horseshoe_base_π A).3 :=
show epi (projective.π _), by apply_instance

--show epi (biprod.desc (projective.π _ ≫ A.f) ((projective.factor_thru (projective.π _) A.g))), by apply_instance

variables {A B}

def horseshoe_ker [epi f.1] : short_exact_sequence C :=
(snake_input.mk_of_short_exact_sequence_hom _ _ _ f).kernel_sequence _
begin
  dsimp [snake_input.mk_of_short_exact_sequence_hom, snake_diagram.mk_of_short_exact_sequence_hom],
  rw snake_diagram.mk_functor_map_f1,
  exact A.mono',
end
$ is_zero_of_iso_of_zero (is_zero_zero _) (limits.cokernel.of_epi _).symm

@[simp] lemma horseshoe_ker_fst [epi f.1] : (horseshoe_ker f).1 = kernel f.1 := rfl

@[simp] lemma horseshoe_ker_snd [epi f.1] : (horseshoe_ker f).2 = kernel f.2 := rfl

@[simp] lemma horseshoe_ker_trd [epi f.1] : (horseshoe_ker f).3 = kernel f.3 := rfl

def horseshoe_ker_ι [epi f.1] : horseshoe_ker f ⟶ A :=
{ fst := kernel.ι _,
  snd := kernel.ι _,
  trd := kernel.ι _,
  sq1' :=
  begin
    dsimp [horseshoe_ker, snake_input.kernel_sequence,
      snake_input.mk_of_short_exact_sequence_hom, snake_diagram.mk_of_short_exact_sequence_hom],
    delta kernel.map,
    rw [snake_diagram.mk_functor_map_f0, kernel.lift_ι],
  end,
  sq2' :=
  begin
    dsimp [horseshoe_ker, snake_input.kernel_sequence,
      snake_input.mk_of_short_exact_sequence_hom, snake_diagram.mk_of_short_exact_sequence_hom],
    delta kernel.map,
    rw [snake_diagram.mk_functor_map_g0, kernel.lift_ι],
  end }
.

lemma horseshoe_ker_ι_fst [epi f.1] : (horseshoe_ker_ι f).1 = kernel.ι f.1 := rfl

lemma horseshoe_ker_ι_snd [epi f.1] : (horseshoe_ker_ι f).2 = kernel.ι f.2 := rfl

lemma horseshoe_ker_ι_trd [epi f.1] : (horseshoe_ker_ι f).3 = kernel.ι f.3 := rfl

variables (A)

lemma horseshoe_ker_ι_comp_base_π :
  (horseshoe_ker_ι (horseshoe_base_π A)) ≫ horseshoe_base_π A = 0 :=
begin
  dsimp [horseshoe_ker_ι, horseshoe_base_π],
  ext1; show kernel.ι _ ≫ _ = 0; apply exact.w,
end

noncomputable
def horseshoe_step (A : short_exact_sequence C) :
  ℕ → Σ (X Y Z : short_exact_sequence C) (ι : X ⟶ Y), Y ⟶ Z
| 0     := ⟨horseshoe_ker (horseshoe_base_π A), _, _, horseshoe_ker_ι _, horseshoe_base_π _⟩
| (n+1) :=
⟨horseshoe_ker (horseshoe_base_π (horseshoe_step n).1), _, _, horseshoe_ker_ι _, horseshoe_base_π _⟩

@[reassoc] lemma horseshoe_step_comp_eq_zero :
  ∀ n, (horseshoe_step A n).2.2.2.1 ≫ (horseshoe_step A n).2.2.2.2 = 0
| 0     := horseshoe_ker_ι_comp_base_π _
| (n+1) := horseshoe_ker_ι_comp_base_π _

lemma step_fst_mono (n : ℕ) : mono (horseshoe_step A n).2.2.2.1.1 :=
begin
  cases n,
  { dsimp [horseshoe_step, horseshoe_ker_ι],
    apply_instance },
  { dsimp [horseshoe_step],
    cases n, --Why do I have to do this again?!
    { rw [horseshoe_ker_ι_fst],
      apply_instance },
    { rw [horseshoe_ker_ι_fst],
      apply_instance }  }
end

lemma step_snd_mono (n : ℕ) : mono (horseshoe_step A n).2.2.2.1.2 :=
begin
  cases n,
  { dsimp [horseshoe_step, horseshoe_ker_ι],
    apply_instance },
  { dsimp [horseshoe_step],
    cases n, --Why do I have to do this again?!
    { rw [horseshoe_ker_ι_snd],
      apply_instance },
    { rw [horseshoe_ker_ι_snd],
      apply_instance }  }
end

lemma step_trd_mono (n : ℕ) : mono (horseshoe_step A n).2.2.2.1.3 :=
begin
  cases n,
  { dsimp [horseshoe_step, horseshoe_ker_ι],
    apply_instance },
  { dsimp [horseshoe_step],
    cases n, --Why do I have to do this again?!
    { rw [horseshoe_ker_ι_trd],
      apply_instance },
    { rw [horseshoe_ker_ι_trd],
      apply_instance }  }
end

def horseshoe_obj (n : ℕ) := (horseshoe_step A n).2.1

def horseshoe_d (n : ℕ) : horseshoe_obj A (n+1) ⟶ horseshoe_obj A n :=
(horseshoe_step A (n+1)).2.2.2.2 ≫ eq_to_hom (by { dsimp [horseshoe_step], refl })
  ≫ (horseshoe_step A n).2.2.2.1

lemma horseshoe_d_d (n : ℕ) : horseshoe_d A (n+1) ≫ horseshoe_d A n = 0 :=
begin
  dsimp [horseshoe_d, horseshoe_ker_ι],
  simp only [category.id_comp, category.assoc, comp_zero, zero_comp,
    horseshoe_step_comp_eq_zero_assoc],
end

def horseshoe (A : short_exact_sequence C) : chain_complex (short_exact_sequence C) ℕ :=
chain_complex.of (horseshoe_obj A) (horseshoe_d A) (horseshoe_d_d A)

variables (A)

def horseshoe_π : (horseshoe A).X 0 ⟶ A := horseshoe_base_π _

lemma horseshoe_d_π : (horseshoe A).d 1 0 ≫ horseshoe_π A = 0 :=
begin
  dsimp [horseshoe],
  erw [chain_complex.of_d],
  dsimp [horseshoe_d, horseshoe_π, horseshoe_step],
  simp only [category.id_comp, category.assoc, comp_zero, zero_comp,
    horseshoe_step_comp_eq_zero_assoc, horseshoe_ker_ι_comp_base_π],
end

def horseshoe_to_single₁ :=
(chain_complex.to_single₀_equiv ((homological_complex.Fst C).obj (horseshoe A)) A.1).symm
⟨(short_exact_sequence.Fst C).map (horseshoe_π A),
begin
  have := horseshoe_d_π A, apply_fun (λ f, (short_exact_sequence.Fst C).map f) at this,
  rwa [functor.map_comp, functor.map_zero] at this,
end⟩

def horseshoe_to_single₂ :=
(chain_complex.to_single₀_equiv ((homological_complex.Snd C).obj (horseshoe A)) A.2).symm
⟨(short_exact_sequence.Snd C).map (horseshoe_π A),
begin
  have := horseshoe_d_π A, apply_fun (λ f, (short_exact_sequence.Snd C).map f) at this,
  rwa [functor.map_comp, functor.map_zero] at this,
end⟩

def horseshoe_to_single₃ :=
(chain_complex.to_single₀_equiv ((homological_complex.Trd C).obj (horseshoe A)) A.3).symm
⟨(short_exact_sequence.Trd C).map (horseshoe_π A),
begin
  have := horseshoe_d_π A, apply_fun (λ f, (short_exact_sequence.Trd C).map f) at this,
  rwa [functor.map_comp, functor.map_zero] at this,
end⟩

lemma horseshoe_exact₁ (A : short_exact_sequence C) (n : ℕ) :
  exact (((homological_complex.Fst C).obj (horseshoe A)).d (n + 2) (n + 1))
    (((homological_complex.Fst C).obj (horseshoe A)).d (n + 1) n) :=
begin
  dsimp [horseshoe_to_single₁],
  erw [chain_complex.of_d, chain_complex.of_d],
  dsimp [horseshoe_d, horseshoe_step],

  set f := horseshoe_base_π (horseshoe_step A n).1,
  set g := (horseshoe_step A n).2.2.2.1,

  cases n;
  convert exact_of_epi_comp_kernel.ι_comp_mono f.1 _ (horseshoe_base_π (horseshoe_ker f)).1 _
    infer_instance _ _ using 1,
  { simp [step_fst_mono] },
  { simpa },
  { simp [step_fst_mono] },
  { simpa }
end

lemma horseshoe_exact₂ (A : short_exact_sequence C) (n : ℕ) :
  exact (((homological_complex.Snd C).obj (horseshoe A)).d (n + 2) (n + 1))
    (((homological_complex.Snd C).obj (horseshoe A)).d (n + 1) n) :=
begin
  dsimp [horseshoe_to_single₂],
  erw [chain_complex.of_d, chain_complex.of_d],
  dsimp [horseshoe_d, horseshoe_step],

  set f := horseshoe_base_π (horseshoe_step A n).1,
  set g := (horseshoe_step A n).2.2.2.1,

  cases n;
  convert exact_of_epi_comp_kernel.ι_comp_mono f.2 _ (horseshoe_base_π (horseshoe_ker f)).2 _
    infer_instance _ _ using 1,
  { simp [step_snd_mono] },
  { simpa },
  { simp [step_snd_mono] },
  { simpa }
end

lemma horseshoe_exact₃ (A : short_exact_sequence C) (n : ℕ) :
  exact (((homological_complex.Trd C).obj (horseshoe A)).d (n + 2) (n + 1))
    (((homological_complex.Trd C).obj (horseshoe A)).d (n + 1) n) :=
begin
  dsimp [horseshoe_to_single₃],
  erw [chain_complex.of_d, chain_complex.of_d],
  dsimp [horseshoe_d, horseshoe_step],

  set f := horseshoe_base_π (horseshoe_step A n).1,
  set g := (horseshoe_step A n).2.2.2.1,

  cases n;
  convert exact_of_epi_comp_kernel.ι_comp_mono f.3 _ (horseshoe_base_π (horseshoe_ker f)).3 _
    infer_instance _ _ using 1,
  { simp [step_trd_mono] },
  { simpa },
  { simp [step_trd_mono] },
  { simpa }
end

lemma horseshoe_is_projective_resolution₁ (A : short_exact_sequence C) :
  chain_complex.is_projective_resolution
    ((homological_complex.Fst C).obj (horseshoe A)) A.1 (horseshoe_to_single₁ A) :=
{ projective := by rintro (_|n); { show projective (projective.over _), apply_instance },
  exact₀ :=
  begin
    dsimp [horseshoe_to_single₁, chain_complex.to_single₀_equiv, horseshoe_π],
    erw [chain_complex.of_d],
    dsimp [horseshoe_d, horseshoe_step],
    rw [category.id_comp, ← short_exact_sequence.comp_fst],
    refine abelian.pseudoelement.exact_of_pseudo_exact _ _ ⟨λ a , _, λ a ha, _⟩,
    { rw [← abelian.pseudoelement.comp_apply, ← short_exact_sequence.comp_fst, category.assoc,
        horseshoe_ker_ι_comp_base_π, comp_zero, short_exact_sequence.hom_zero_fst,
        abelian.pseudoelement.zero_apply] },
    { obtain ⟨b, hb⟩ := is_snake_input.exists_of_exact exact_kernel_ι _ ha,
      obtain ⟨c, hc⟩ := abelian.pseudoelement.pseudo_surjective_of_epi
        (horseshoe_base_π (horseshoe_ker _)).1 b,
      refine ⟨c, _⟩,
      rw [short_exact_sequence.comp_fst, abelian.pseudoelement.comp_apply, hc, ← hb],
      refl }
  end,
  exact := λ n, horseshoe_exact₁ A n,
  epi := show epi (projective.π _), from infer_instance }

lemma horseshoe_is_projective_resolution₂ (A : short_exact_sequence C) :
  chain_complex.is_projective_resolution
    ((homological_complex.Snd C).obj (horseshoe A)) A.2 (horseshoe_to_single₂ A) :=
{ projective := by rintro (_|n); { show projective (projective.over _ ⊞ projective.over _),
    apply_instance },
  exact₀ :=
  begin
    dsimp [horseshoe_to_single₂, chain_complex.to_single₀_equiv, horseshoe_π],
    erw [chain_complex.of_d],
    dsimp [horseshoe_d, horseshoe_step],
    rw [category.id_comp, ← short_exact_sequence.comp_snd],
    refine abelian.pseudoelement.exact_of_pseudo_exact _ _ ⟨λ a , _, λ a ha, _⟩,
    { rw [← abelian.pseudoelement.comp_apply, ← short_exact_sequence.comp_snd, category.assoc,
        horseshoe_ker_ι_comp_base_π, comp_zero, short_exact_sequence.hom_zero_snd,
        abelian.pseudoelement.zero_apply] },
    { obtain ⟨b, hb⟩ := is_snake_input.exists_of_exact exact_kernel_ι _ ha,
      obtain ⟨c, hc⟩ := abelian.pseudoelement.pseudo_surjective_of_epi
        (horseshoe_base_π (horseshoe_ker _)).2 b,
      refine ⟨c, _⟩,
      rw [short_exact_sequence.comp_snd, abelian.pseudoelement.comp_apply, hc, ← hb],
      refl }
  end,
  exact := λ n, horseshoe_exact₂ A n,
  epi := show epi (horseshoe_base_π _).2, from infer_instance }

lemma horseshoe_is_projective_resolution₃ (A : short_exact_sequence C) :
  chain_complex.is_projective_resolution
    ((homological_complex.Trd C).obj (horseshoe A)) A.3 (horseshoe_to_single₃ A) :=
{ projective := by rintro (_|n); { show projective (projective.over _), apply_instance },
  exact₀ :=
  begin
    dsimp [horseshoe_to_single₃, chain_complex.to_single₀_equiv, horseshoe_π],
    erw [chain_complex.of_d],
    dsimp [horseshoe_d, horseshoe_step],
    rw [category.id_comp, ← short_exact_sequence.comp_trd],
    refine abelian.pseudoelement.exact_of_pseudo_exact _ _ ⟨λ a , _, λ a ha, _⟩,
    { rw [← abelian.pseudoelement.comp_apply, ← short_exact_sequence.comp_trd, category.assoc,
        horseshoe_ker_ι_comp_base_π, comp_zero, short_exact_sequence.hom_zero_trd,
        abelian.pseudoelement.zero_apply] },
    { obtain ⟨b, hb⟩ := is_snake_input.exists_of_exact exact_kernel_ι _ ha,
      obtain ⟨c, hc⟩ := abelian.pseudoelement.pseudo_surjective_of_epi
        (horseshoe_base_π (horseshoe_ker _)).3 b,
      refine ⟨c, _⟩,
      rw [short_exact_sequence.comp_trd, abelian.pseudoelement.comp_apply, hc, ← hb],
      refl }
  end,
  exact := λ n, horseshoe_exact₃ A n,
  epi := show epi (projective.π _), from infer_instance }

end short_exact_sequence
