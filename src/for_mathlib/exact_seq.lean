import algebra.homology.exact
import category_theory.abelian.opposite
import category_theory.abelian.exact
import category_theory.limits.constructions.epi_mono
import category_theory.abelian.pseudoelements

noncomputable theory

open category_theory
open category_theory.limits

universes w v u

namespace list

variables {α : Type*} (a : α) (L : list α) (m n : ℕ)

/-- Returns the sublist of `L` starting at index `m` of length `n`
(or shorter, if `L` is too short). -/
def extract := (L.drop m).take n

@[simp] lemma extract_nil : [].extract m n = ([] : list α) :=
by { cases n, refl, cases m, refl, refl }

@[simp] lemma extract_zero_right : L.extract m 0 = [] := rfl

@[simp] lemma extract_cons_succ_left : (a :: L).extract m.succ n = L.extract m n := rfl

end list

example : [0,1,2,3,4,5,6,7,8,9].extract 4 3 = [4,5,6] := rfl

namespace category_theory
variables (𝒞 : Type u) [category.{v} 𝒞]
variables [has_zero_morphisms 𝒞] [has_images 𝒞] [has_kernels 𝒞]
variables {𝒜 : Type u} [category.{v} 𝒜] [abelian 𝒜]

namespace exact -- move this

variables {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C)

def kernel_op_iso : (kernel f.op).unop ≅ cokernel f :=
{ hom := (kernel.lift _ (cokernel.π f).op begin
    simp [← op_comp, limits.cokernel.condition],
  end).unop ≫ eq_to_hom (opposite.unop_op (cokernel f)),
  inv := cokernel.desc _ (eq_to_hom (opposite.unop_op B).symm ≫ (kernel.ι f.op).unop) begin
    dsimp,
    rw [category.id_comp, ← f.unop_op, ← unop_comp, f.unop_op, kernel.condition],
    refl,
  end,
  hom_inv_id' := begin
    dsimp,
    simp,
    rw [← unop_id, ← (cokernel.desc f (kernel.ι f.op).unop _).unop_op, ← unop_comp],
    congr' 1,
    apply limits.equalizer.hom_ext,
    dsimp,
    simp [← op_comp],
  end,
  inv_hom_id' := begin
    apply limits.coequalizer.hom_ext,
    dsimp,
    simp [← unop_comp],
  end }

def cokernel_op_iso : (cokernel f.op).unop ≅ kernel f :=
{ hom := kernel.lift _ ((cokernel.π f.op).unop ≫ eq_to_hom (opposite.unop_op _)) begin
    simp only [eq_to_hom_refl, category.comp_id],
    rw [← f.unop_op, ← unop_comp, f.op.op_unop, cokernel.condition],
    refl,
  end,
  inv := eq_to_hom (opposite.unop_op _).symm ≫ (cokernel.desc _ (kernel.ι f).op (by simp [← op_comp])).unop,
  hom_inv_id' := begin
    simp only [category.id_comp, eq_to_hom_refl, category.comp_id, ← unop_id, ← unop_comp],
    rw [← (kernel.lift f (cokernel.π f.op).unop _).unop_op, ← unop_comp],
    congr' 1,
    apply limits.coequalizer.hom_ext,
    dsimp,
    simp [← op_comp],
  end,
  inv_hom_id' := begin
    apply limits.equalizer.hom_ext,
    dsimp,
    simp [← unop_comp]
  end } .

@[simp]
lemma kernel.ι_op : (kernel.ι f.op).unop =
  eq_to_hom (opposite.unop_op _) ≫ cokernel.π f ≫ (kernel_op_iso f).inv :=
begin
  dsimp [kernel_op_iso],
  simp,
end

@[simp]
lemma cokernel.π_op : (cokernel.π f.op).unop =
  (cokernel_op_iso f).hom ≫ kernel.ι f ≫ eq_to_hom (opposite.unop_op _).symm :=
begin
  dsimp [cokernel_op_iso],
  simp,
end

instance [exact f g] : exact g.op f.op :=
begin
  rw abelian.exact_iff,
  refine ⟨by simp [← op_comp], _⟩,
  apply_fun quiver.hom.unop,
  swap, { exact quiver.hom.unop_inj },
  simp,
end

def kernel_unop_iso {C B : 𝒜ᵒᵖ} (f : C ⟶ B) : opposite.op (kernel f.unop) ≅ cokernel f :=
{ hom := (kernel.lift _ (cokernel.π f).unop (by simp [← unop_comp])).op ≫
    eq_to_hom (opposite.op_unop (cokernel f)),
  inv := cokernel.desc _ (eq_to_hom (opposite.op_unop _).symm ≫ (kernel.ι f.unop).op) begin
    dsimp,
    rw [← f.op_unop, category.id_comp, ← op_comp, f.op_unop, kernel.condition],
    refl,
  end,
  hom_inv_id' := begin
    dsimp,
    simp,
    rw [← (cokernel.desc f (kernel.ι f.unop).op _).op_unop, ← op_comp, ← op_id],
    congr' 1,
    apply limits.equalizer.hom_ext,
    dsimp,
    simp [← unop_comp],
  end,
  inv_hom_id' := begin
    apply limits.coequalizer.hom_ext,
    dsimp,
    simp [← op_comp],
  end }

def cokernel_unop_iso {C B : 𝒜ᵒᵖ} (f : C ⟶ B) : opposite.op (cokernel f.unop) ≅ kernel f :=
{ hom := kernel.lift _ ((cokernel.π f.unop).op ≫ eq_to_hom (opposite.op_unop _)) begin
    dsimp,
    rw [← f.op_unop, category.comp_id, ← op_comp, f.op_unop, cokernel.condition],
    refl,
  end,
  inv := eq_to_hom (opposite.op_unop _).symm ≫
    (cokernel.desc _ (kernel.ι f).unop (by simp [← unop_comp])).op,
  hom_inv_id' := begin
    dsimp,
    rw category.id_comp,
    rw [← (kernel.lift f ((cokernel.π f.unop).op ≫ 𝟙 C) _).op_unop, ← op_comp, ← op_id],
    congr' 1,
    apply limits.coequalizer.hom_ext,
    dsimp,
    simp [← unop_comp],
  end,
  inv_hom_id' := begin
    apply limits.equalizer.hom_ext,
    dsimp,
    simp [← op_comp]
  end }

@[simp]
lemma cokernel.π_unop {C B : 𝒜ᵒᵖ} (f : C ⟶ B) : (cokernel.π f.unop).op =
  (cokernel_unop_iso f).hom ≫ kernel.ι f ≫ eq_to_hom (opposite.op_unop _).symm :=
begin
  dsimp [cokernel_unop_iso],
  simp,
end

@[simp]
lemma kernel.ι_unop {C B : 𝒜ᵒᵖ} (f : C ⟶ B) : (kernel.ι f.unop).op =
  eq_to_hom (opposite.op_unop _) ≫ cokernel.π f ≫ (kernel_unop_iso f).inv :=
begin
  dsimp [kernel_unop_iso],
  simp,
end

instance {C B A : 𝒜ᵒᵖ} (g : C ⟶ B) (f : B ⟶ A) [exact g f] : exact f.unop g.unop :=
begin
  rw abelian.exact_iff,
  refine ⟨by simp [← unop_comp], _⟩,
  apply_fun quiver.hom.op,
  swap, { exact quiver.hom.op_inj },
  simp,
end

end exact

/-- A sequence `[f, g, ...]` of morphisms is exact if the pair `(f,g)` is exact,
and the sequence `[g, ...]` is exact.

Recall that the pair `(f,g)` is exact if `f ≫ g = 0`
and the natural map from the image of `f` to the kernel of `g` is an epimorphism
(equivalently, in abelian categories: isomorphism). -/
inductive exact_seq : list (arrow 𝒞) → Prop
| nil    : exact_seq []
| single : ∀ f, exact_seq [f]
| cons   : ∀ {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (hfg : exact f g) (L) (hgL : exact_seq (g :: L)),
              exact_seq (f :: g :: L)

variable {𝒞}

lemma exact_iff_exact_seq {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ exact_seq 𝒞 [f, g] :=
begin
  split,
  { intro h, exact exact_seq.cons f g h _ (exact_seq.single _), },
  { rintro (_ | _ | ⟨A, B, C, f, g, hfg, _, _ | _ | _⟩), exact hfg, }
end

namespace exact_seq

lemma extract : ∀ {L : list (arrow 𝒞)} (h : exact_seq 𝒞 L) (m n : ℕ),
  exact_seq 𝒞 (L.extract m n)
| L (nil)               m     n     := by { rw list.extract_nil, exact nil }
| L (single f)          m     0     := nil
| L (single f)          0     (n+1) := by { cases n; exact single f }
| L (single f)          (m+1) (n+1) := by { cases m; exact nil }
| _ (cons f g hfg L hL) (m+1) n     := extract hL m n
| _ (cons f g hfg L hL) 0     0     := nil
| _ (cons f g hfg L hL) 0     1     := single f
| _ (cons f g hfg L hL) 0     (n+2) := cons f g hfg (L.take n) (extract hL 0 (n+1))

inductive arrow_congr : Π (L L' : list (arrow 𝒞)), Prop
| nil  : arrow_congr [] []
| cons : ∀ {A B : 𝒞} {f f' : A ⟶ B} {L L' : list (arrow 𝒞)} (h : f = f') (H : arrow_congr L L'),
         arrow_congr (f :: L) (f' :: L')

lemma congr : ∀ {L L' : list (arrow 𝒞)}, exact_seq 𝒞 L → arrow_congr L L' → exact_seq 𝒞 L'
| _ _ h arrow_congr.nil                                 := exact_seq.nil
| _ _ h (arrow_congr.cons h₁ arrow_congr.nil)           := exact_seq.single _
| _ _ h (arrow_congr.cons h₁ ((arrow_congr.cons h₂ H))) :=
begin
  substs h₁ h₂,
  rcases h with _ | _ | ⟨A, B, C, f, g, hfg, _, hL⟩,
  refine exact_seq.cons _ _ hfg _ (congr hL (arrow_congr.cons rfl H)),
end

lemma append : ∀ {L₁ L₂ L₃ : list (arrow 𝒞)}
  (h₁₂ : exact_seq 𝒞 (L₁ ++ L₂)) (h₂₃ : exact_seq 𝒞 (L₂ ++ L₃)) (h₂ : L₂ ≠ []),
  exact_seq 𝒞 (L₁ ++ L₂ ++ L₃)
| L₁         []      L₃ h₁₂                 h₂₃ h := (h rfl).elim
| []         L₂      L₃ h₁₂                 h₂₃ h := by rwa list.nil_append
| (_::[])    (_::L₂) L₃ (cons f g hfg L hL) h₂₃ h := cons f g hfg _ h₂₃
| (_::_::L₁) L₂      L₃ (cons f g hfg L hL) h₂₃ h :=
suffices exact_seq 𝒞 ([f] ++ ([g] ++ L₁ ++ L₂) ++ L₃), { simpa only [list.append_assoc] },
cons _ _ hfg _ $
suffices exact_seq 𝒞 ((g :: L₁) ++ L₂ ++ L₃), { simpa only [list.append_assoc] },
append (by simpa only using hL) h₂₃ h

end exact_seq

namespace arrow

open _root_.opposite

variables {C : Type*} [category C]

@[simps]
def op (f : arrow C) : arrow Cᵒᵖ :=
{ left := op f.right,
  right := op f.left,
  hom := f.hom.op }

@[simps]
def unop (f : arrow Cᵒᵖ) : arrow C :=
{ left := unop f.right,
  right := unop f.left,
  hom := f.hom.unop }

@[simp] lemma op_unop (f : arrow C)   : f.op.unop = f := by { cases f, dsimp [op, unop], refl }
@[simp] lemma unop_op (f : arrow Cᵒᵖ) : f.unop.op = f := by { cases f, dsimp [op, unop], refl }

@[simp] lemma op_comp_unop : (op ∘ unop : arrow Cᵒᵖ → arrow Cᵒᵖ) = id := by { ext, exact unop_op _ }
@[simp] lemma unop_comp_op : (unop ∘ op : arrow C   → arrow C  ) = id := by { ext, exact op_unop _ }

end arrow

namespace exact_seq

lemma op : ∀ {L : list (arrow 𝒜)}, exact_seq 𝒜 L → exact_seq 𝒜ᵒᵖ (L.reverse.map arrow.op)
| _ nil                 := nil
| _ (single f)          := single f.op
| _ (cons f g hfg L hL) :=
begin
  have hgf : exact g.op f.op, { resetI, apply_instance },
  have := op hL,
  simp only [list.reverse_cons, list.map_append] at this ⊢,
  refine this.append _ (list.cons_ne_nil _ _),
  exact cons _ _ hgf _ (single _),
end

lemma unop : ∀ {L : list (arrow 𝒜ᵒᵖ)}, exact_seq 𝒜ᵒᵖ L → exact_seq 𝒜 (L.reverse.map arrow.unop)
| _ nil                 := nil
| _ (single f)          := single f.unop
| _ (cons f g hfg L hL) :=
begin
  have hgf : exact g.unop f.unop, { resetI, apply_instance },
  have := unop hL,
  simp only [list.reverse_cons, list.map_append] at this ⊢,
  refine this.append _ (list.cons_ne_nil _ _),
  exact cons _ _ hgf _ (single _),
end

lemma of_op {L : list (arrow 𝒜)} (h : exact_seq 𝒜ᵒᵖ (L.reverse.map arrow.op)) : exact_seq 𝒜 L :=
by simpa only [list.map_reverse, list.reverse_reverse, list.map_map,
  arrow.unop_comp_op, list.map_id] using h.unop

lemma of_unop {L : list (arrow 𝒜ᵒᵖ)} (h : exact_seq 𝒜 (L.reverse.map arrow.unop)) :
  exact_seq 𝒜ᵒᵖ L :=
by simpa only [list.map_reverse, list.reverse_reverse, list.map_map,
  arrow.op_comp_unop, list.map_id] using h.op

end exact_seq

end category_theory

namespace category_theory

open functor

variables {C : Type u} {D : Type v} [category.{w} C] [category.{w} D]
variables {F : C ⥤ D} {A₁ A₂ A₃ X : C} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}
variables [abelian C] [abelian D] [additive F] (ex : exact_seq C [f, g, (0 : A₃ ⟶ X)])

namespace functor.right_exact

variable (F)
def cokernel_diagram_iso {A B : C} (f : A ⟶ B) :
  parallel_pair f 0 ⋙ F ≅ parallel_pair (F.map f) 0 :=
nat_iso.of_components (λ X,
  match X with
  | walking_parallel_pair.zero := iso.refl _
  | walking_parallel_pair.one := iso.refl _
  end)
begin
  rintros (a|a) (b|b) (f|f),
  work_on_goal 0 { dsimp at *, simp at *, dsimp at *, simp at * },
  work_on_goal 0 { dsimp at *, unfold_aux, dsimp at *, simp at * },
  work_on_goal 0 { dsimp at *, simp at * },
  dsimp at *, simp at *, dsimp at *, simp at *,
end

def preserves_cokernel [limits.preserves_finite_colimits F] {A B : C} (f : A ⟶ B) :
  F.obj (cokernel f) ≅ cokernel (F.map f) :=
(is_colimit_of_preserves _ (colimit.is_colimit _)).cocone_point_unique_up_to_iso
  (colimit.is_colimit _) ≪≫ limits.has_colimit.iso_of_nat_iso
  (cokernel_diagram_iso _ _)

@[simp, reassoc]
lemma map_preserves_cokernel_hom [limits.preserves_finite_colimits F] :
  F.map (cokernel.π f) ≫ (preserves_cokernel F f).hom = cokernel.π (F.map f) :=
begin
  erw (is_colimit_of_preserves F (colimit.is_colimit (parallel_pair f 0))).fac_assoc,
  dsimp, simp only [has_colimit.iso_of_nat_iso_ι_hom],
  dsimp [cokernel_diagram_iso],
  simp,
end

variable {F}

include ex

-- Do we have some API with `exact_seq` to get lemmas like this?
lemma comp_eq_zero : f ≫ g = 0 :=
begin
  suffices : exact f g, by exact this.1,
  rw exact_iff_exact_seq,
  exact ex.extract 0 2,
end

variable (F)
lemma map_comp_eq_zero : F.map f ≫ F.map g = 0 :=
by { rw [← F.map_comp, comp_eq_zero ex], simp }

variable {F}

def cokernel_comparison : cokernel f ⟶ A₃ :=
  cokernel.desc f g $ comp_eq_zero ex

local attribute [instance] abelian.pseudoelement.over_to_sort
  abelian.pseudoelement.hom_to_fun
  abelian.pseudoelement.has_zero

instance [epi g] : is_iso (cokernel_comparison ex) :=
begin
  refine (is_iso_iff_mono_and_epi _).2 ⟨_, limits.cokernel.desc_epi _ _ _⟩,
  refine abelian.pseudoelement.mono_of_zero_of_map_zero _ (λ a ha, _),
  obtain ⟨b, hb⟩ := abelian.pseudoelement.pseudo_surjective_of_epi (cokernel.π f) a,
  have hbz : g b = 0,
  { have : g = (cokernel.π f) ≫ (cokernel_comparison ex) := (cokernel.π_desc _ _ _).symm,
    rw [this, abelian.pseudoelement.comp_apply, hb, ha] },
  obtain ⟨c, hc : f c = b⟩ := abelian.pseudoelement.pseudo_exact_of_exact.2 _ hbz,
  { rw [← hc, ← abelian.pseudoelement.comp_apply, cokernel.condition,
      abelian.pseudoelement.zero_apply] at hb,
    exact hb.symm },
  { exact (exact_iff_exact_seq _ _).2 (ex.extract 0 2) }
end

@[simp, reassoc]
lemma cokernel_comparison_inv [epi g] :
  g ≫ inv (cokernel_comparison ex) = cokernel.π _ :=
begin
  rw is_iso.comp_inv_eq,
  dsimp [cokernel_comparison],
  simp,
end

lemma aux [limits.preserves_finite_colimits F] [epi g] :
  F.map g ≫ (F.map $ inv (cokernel_comparison ex)) ≫ (preserves_cokernel _ _).hom =
  cokernel.π (F.map f) :=
by simp only [← category.assoc, ← F.map_comp, cokernel_comparison_inv, map_preserves_cokernel_hom]

variable (F)

lemma preserves_exact_seq [limits.preserves_finite_colimits F] :
  exact_seq D [F.map f, F.map g, (0 : F.obj A₃ ⟶ F.obj X)] :=
begin
  have exact := (exact_iff_exact_seq _ _).2 (ex.extract 0 2),
  haveI epi : epi g,
  { replace ex : exact_seq C ([g, _]) := ex.extract 1 2,
    rwa [← exact_iff_exact_seq, ← (abelian.tfae_epi X g).out 0 2] at ex },
  refine exact_seq.cons _ _ _ _ _,
  { let I : F.obj A₃ ≅ cokernel (F.map f) :=
      (F.map_iso $ (as_iso $ cokernel_comparison ex).symm) ≪≫ preserves_cokernel _ _,
    suffices : category_theory.exact (F.map f) (F.map g ≫ I.hom), by rwa exact_comp_iso at this,
    erw aux,
    exact abelian.exact_cokernel (F.map f) },
  rw [← exact_iff_exact_seq, ← (abelian.tfae_epi (F.obj X) (F.map g)).out 0 2],
  exact category_theory.preserves_epi _ _,
end

end functor.right_exact

end category_theory
