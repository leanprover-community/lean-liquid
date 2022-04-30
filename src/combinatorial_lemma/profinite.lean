import combinatorial_lemma.profinite_setup

section

open category_theory
open category_theory.limits
open ProFiltPseuNormGrpWithTinv₁

open_locale nnreal big_operators

noncomputable theory

universe u

variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type u) [polyhedral_lattice Λ] (S : Profinite.{u})

namespace pseudo_normed_group

def sum' {c₁ c₂ : ℝ≥0} {M : Type u} [pseudo_normed_group M]
  (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
  (Π i : fin n, pseudo_normed_group.filtration M c₁) → pseudo_normed_group.filtration M c₂ :=
λ t, ⟨∑ i : fin n, (t i).1, begin
  apply filtration_mono,
  rotate 1,
  apply pseudo_normed_group.sum_mem_filtration,
  intros i hi, exact (t i).2,
  simpa,
end⟩

@[simp] lemma coe_sum' {c₁ c₂ : ℝ≥0} {M : Type u} [pseudo_normed_group M]
  (n : ℕ) (h : ↑n * c₁ ≤ c₂) (t : Π i : fin n, pseudo_normed_group.filtration M c₁) :
  (sum' n h t : M) = ∑ i : fin n, (t i : M) := rfl

lemma sum'_zero {c₁ c₂ : ℝ≥0} {M : Type u} [pseudo_normed_group M] (h : ↑0 * c₁ ≤ c₂) :
  (sum' 0 h :
    (Π i : fin 0, pseudo_normed_group.filtration M c₁) → pseudo_normed_group.filtration M c₂) =
  (λ _, 0) :=
begin
  ext t,
  simp only [sum', fintype.univ_of_is_empty, subtype.val_eq_coe, finset.sum_empty,
    subtype.coe_mk, filtration.coe_zero],
end

lemma sum'_succ {c₁ c₂ : ℝ≥0} {M : Type u} [pseudo_normed_group M] (n : ℕ) (h : ↑(n+1) * c₁ ≤ c₂) :
  (sum' (n+1) h :
    (Π i : fin (n+1), pseudo_normed_group.filtration M c₁) → pseudo_normed_group.filtration M c₂) =
  cast_le' (by simpa [add_mul] using h) ∘ add' ∘ (λ t, ⟨sum' n le_rfl (fin.tail t), t 0⟩) :=
begin
  ext t,
  simp only [sum', subtype.val_eq_coe, subtype.coe_mk, coe_cast_le', add'_eq],
  rw [fin.sum_univ_succ, add_comm],
  refl
end

end pseudo_normed_group

namespace comphaus_filtered_pseudo_normed_group

open pseudo_normed_group

lemma continuous_sum' {c₁ c₂ : ℝ≥0} {M : Type u} [comphaus_filtered_pseudo_normed_group M]
  (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
  continuous (pseudo_normed_group.sum' n h :
    (Π (i : fin n), pseudo_normed_group.filtration M c₁) →
    pseudo_normed_group.filtration M c₂) :=
begin
  have : @pseudo_normed_group.sum' _ _ M _ n h =
    pseudo_normed_group.cast_le' h ∘ pseudo_normed_group.sum' n le_rfl,
  { ext, refl },
  rw this,
  refine (@comphaus_filtered_pseudo_normed_group.continuous_cast_le _ _ _ _ ⟨h⟩).comp _,
  clear this h c₂,
  induction n with n ih,
  { rw [pseudo_normed_group.sum'_zero], exact continuous_const },
  rw pseudo_normed_group.sum'_succ,
  haveI : fact (↑n * c₁ + c₁ ≤ ↑(n.succ) * c₁) :=
    by simp only [nat.cast_succ, add_mul, one_mul]; apply_instance,
  refine (comphaus_filtered_pseudo_normed_group.continuous_cast_le _ _).comp
    ((comphaus_filtered_pseudo_normed_group.continuous_add' _ _).comp _),
  refine continuous.prod_mk (ih.comp _) (continuous_apply _),
  exact continuous_pi (λ i, continuous_apply _),
end

end comphaus_filtered_pseudo_normed_group

/-
namespace Profinite

def pow (X : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
Profinite.product (λ i : fin n, X)

def map_pow {X Y : Profinite.{u}} (f : X ⟶ Y) (n : ℕ) :
  X.pow n ⟶ Y.pow n :=
Profinite.product.lift _ $ λ n, Profinite.product.π _ n ≫ f

end Profinite
-/

namespace ProFiltPseuNormGrpWithTinv₁

@[simps]
def level : ℝ≥0 ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ Profinite.{u} :=
{ obj := λ c,
  { obj := λ X, Profinite.of $ pseudo_normed_group.filtration X c,
    map := λ X Y f, ⟨f.level _, f.continuous' _⟩,
    map_id' := λ M, by { ext, refl },
    map_comp' := λ M₁ M₂ M₃ f g, by { ext, refl } },
  map := λ c₁ c₂ h,
  { app := λ X, ⟨pseudo_normed_group.cast_le' h.le, begin
      haveI : fact (c₁ ≤ c₂) := ⟨h.le⟩,
      apply comphaus_filtered_pseudo_normed_group.continuous_cast_le,
    end⟩,
    naturality' := λ M₁ M₂ f, by { ext, refl } },
  map_id' := λ c, by { ext, refl },
  map_comp' := λ c₁ c₂ c₃ h₁₂ h₂₃, by { ext, refl } }

instance (c) : preserves_limits ((level r').obj c) :=
begin
  change preserves_limits (to_PFPNG₁.{u} r' ⋙ ProFiltPseuNormGrp₁.level.obj.{u} c),
  apply_with limits.comp_preserves_limits { instances := ff },
  constructor, constructor, introsI J _, constructor,
  -- <-- looks like we have `preserves_limit` and not `preserves_limits`, but
  -- it should be trivial to add, if needed.
end

variable {r'}

abbreviation lvl (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (c : ℝ≥0) : Profinite.{u} :=
((level r').obj c).obj X

abbreviation map_lvl {X Y : ProFiltPseuNormGrpWithTinv₁.{u} r'} (f : X ⟶ Y) (c : ℝ≥0) :
  X.lvl c ⟶ Y.lvl c := ((level r').obj c).map f

@[reassoc] lemma map_lvl_comp {X Y Z : ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (f : X ⟶ Y) (g : Y ⟶ Z) (c : ℝ≥0) :
  map_lvl f c ≫ map_lvl g c = map_lvl (f ≫ g) c :=
by { ext, refl }

abbreviation cast_lvl {c₁ c₂ : ℝ≥0} (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (h : c₁ ≤ c₂) :
  X.lvl c₁ ⟶ X.lvl c₂ := ((level r').map h.hom).app _

@[reassoc] lemma map_lvl_cast_lvl_eq {X Y : ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (f : X ⟶ Y) (c₁ c₂ : ℝ≥0) (h : c₁ ≤ c₂) :
  map_lvl f c₁ ≫ cast_lvl Y h = cast_lvl X h ≫ map_lvl f c₂ :=
by { ext, refl }

def sum {c₁ c₂ : ℝ≥0} (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
  (X.lvl c₁).pow n ⟶ X.lvl c₂ :=
⟨pseudo_normed_group.sum' _ h,
  comphaus_filtered_pseudo_normed_group.continuous_sum' _ _⟩

@[simp] lemma coe_sum {c₁ c₂ : ℝ≥0} (X : ProFiltPseuNormGrpWithTinv₁.{u} r')
  (n : ℕ) (h : ↑n * c₁ ≤ c₂) : ⇑(X.sum n h) = pseudo_normed_group.sum' n h := rfl

lemma le₁ (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) :
  ↑N * (c / ↑N + d) ≤ c + ↑N * d :=
begin
  apply eq.le,
  rw [mul_add, add_left_inj, mul_div_cancel'],
  norm_cast,
  exact ne_of_gt (fact.out _)
end

lemma le₂ (N : ℕ) (c d : ℝ≥0) :
  c ≤ c + ↑N * d := le_self_add

/--
Given a `N : ℕ`, `c : ℝ≥0`, an `X : ProFiltPseuNormGrpWithTinv₁ r'`, and a
  `t : Profinite.punit ⟶ X.lvl c`, this constructs the pullback of `t` along the 2nd projection
  `(X.lvl (c/N + d))^n ×_{X.lvl (c + N * d)} X.lvl c → X.lvl c`.
-/
def gadget (X : ProFiltPseuNormGrpWithTinv₁.{u} r')
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ X.lvl c) : Profinite.{u} :=
Profinite.pullback
(Profinite.pullback.snd (X.sum N (le₁ N c d)) (X.cast_lvl (le₂ N c d))) t

def map_gadget {X Y : ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (f : X ⟶ Y) (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ X.lvl c)
  (t' : Profinite.punit.{u} ⟶ Y.lvl c) (w : t ≫ map_lvl f c = t') :
  X.gadget N c d t ⟶ Y.gadget N c d t' :=
Profinite.pullback.lift _ _
(Profinite.pullback.fst _ _ ≫
  Profinite.pullback.lift _ _
  (Profinite.pullback.fst _ _ ≫
    Profinite.product.lift _ (λ i, Profinite.product.π _ i ≫ map_lvl f _))
  (Profinite.pullback.snd _ _ ≫ map_lvl f _)
  begin
    simp only [category.assoc, map_lvl_cast_lvl_eq, ← Profinite.pullback.condition_assoc],
    ext ⟨⟨x₁, x₂⟩, hx⟩,
    simp only [category.assoc, Profinite.coe_comp, function.comp_app, nat_trans.naturality],
    dsimp [Profinite.pullback.fst, Profinite.pullback.snd],
    rw [f.map_sum, finset.sum_congr rfl],
    rintro i -,
    refl
  end)
(Profinite.pullback.snd _ _)
(by rw [category.assoc, Profinite.pullback.lift_snd, Profinite.pullback.condition_assoc, w])
.

lemma map_gadget_comp {X Y Z : ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (f : X ⟶ Y) (g : Y ⟶ Z) (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ X.lvl c)
  (t' : Profinite.punit.{u} ⟶ Y.lvl c) (t'' : Profinite.punit.{u} ⟶ Z.lvl c)
  (w : t ≫ map_lvl f c = t') (w' : t' ≫ map_lvl g c = t'') :
  map_gadget f N c d t t' w ≫ map_gadget g N c d t' t'' w' =
  map_gadget (f ≫ g) N c d t t'' (by { subst t'', subst t', rw [category.assoc, map_lvl_comp] }) :=
begin
  dsimp only [map_gadget],
  refine Profinite.pullback.hom_ext _ _ _ _ _ _;
  simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
    Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc],
  refl
end

@[simps]
def gadget_diagram {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  J ⥤ Profinite.{u} :=
{ obj := λ j, (K.obj j).gadget N c d (t ≫ map_lvl (C.π.app _) c),
  map := λ i j f, map_gadget (K.map f) _ _ _ _ _ (by rw [category.assoc, map_lvl_comp, cone.w]),
  map_id' := λ i, by { simp only [K.map_id], ext; refl },
  map_comp' := λ i j k h₁ h₂, by { simp only [K.map_comp], ext; refl } }

@[simps]
def gadget_diagram_fst_snd {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  gadget_diagram C N c d t ⟶ K ⋙ (level r').obj c :=
{ app := λ j, Profinite.pullback.fst _ _ ≫ Profinite.pullback.snd _ _,
  naturality' := λ i j h, by { ext; refl } }

@[simps]
def gadget_diagram_fst_fst {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c)
  (i : fin N) :
  gadget_diagram C N c d t ⟶ K ⋙ (level r').obj (c / ↑N + d) :=
{ app := λ j, Profinite.pullback.fst _ _ ≫ Profinite.pullback.fst _ _ ≫
    Profinite.product.π _ i,
  naturality' := λ i j h, by { ext; refl } }

@[simps]
def gadget_cone {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  cone (gadget_diagram C N c d t) :=
{ X := C.X.gadget N c d t,
  π :=
  { app := λ j, map_gadget (C.π.app _) _ _ _ _ _ rfl,
    naturality' := λ i j h,
      by { dsimp, rw [category.id_comp, map_gadget_comp], congr, rw cone.w, } } }

lemma gadget_cone_lift_fst_snd {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (hC : ∀ a : ℝ≥0, is_limit (((level r').obj a).map_cone C))
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c)
  (S : cone (gadget_diagram C N c d t)) :
  (hC c).lift ((cones.postcompose (gadget_diagram_fst_snd C N c d t)).obj S) =
    Profinite.punit.elim S.X ≫ t :=
begin
  refine ((hC c).uniq ((cones.postcompose (gadget_diagram_fst_snd.{u} C N c d t)).obj S) _ _).symm,
  intro j,
  simp only [functor.map_cone_π_app, cones.postcompose_obj_π, nat_trans.comp_app,
    gadget_diagram_fst_snd_app, Profinite.pullback.condition],
  simp only [← category.assoc], congr' 2, ext,
end

lemma gadget_cone_lift_aux {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (hC : ∀ a : ℝ≥0, is_limit (((level r').obj a).map_cone C))
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c)
  (S : cone (gadget_diagram C N c d t)) :
  let η := λ i, (gadget_diagram_fst_fst C N c d t i),
      γ := gadget_diagram_fst_snd C N c d t,
      S' := λ i, (cones.postcompose (η i)).obj S,
      F : Π i, S.X ⟶ _  := λ i, (hC _).lift (S' i),
      S'' :=  (cones.postcompose γ).obj S in
  Profinite.product.lift (λ (i : fin N), C.X.lvl (c / ↑N + d)) F ≫
    C.X.sum N (le₁ _ _ _) = (hC c).lift S'' ≫ C.X.cast_lvl (le₂ _ _ _) :=
begin
  have h₁ := le₁ N c d,
  have h₂ := le₂ N c d,
  rintros η γ S' F S'',
  let γ' : gadget_diagram C N c d t ⟶ K ⋙ (level r').obj (c + ↑N * d) :=
    γ ≫ whisker_left _ ((level r').map h₂.hom),
  let T'' := (cones.postcompose γ').obj S,
  have : (hC c).lift S'' ≫ C.X.cast_lvl h₂ = (hC _).lift T'',
  { apply (hC _).uniq T'',
    intros j,
    have := (hC c).fac S'' j,
    dsimp at this ⊢,
    simp [category.assoc, ← reassoc_of this] },
  rw this,
  apply (hC (c + ↑N * d)).uniq T'',
  intros j,
  dsimp,
  simp only [category.assoc],
  have : C.X.sum N h₁ ≫ ((level r').obj (c + ↑N * d)).map (C.π.app j) =
    Profinite.product.lift _ (λ i, Profinite.product.π _ i ≫ map_lvl (C.π.app _) _) ≫
    ProFiltPseuNormGrpWithTinv₁.sum _ N h₁,
  { ext x,
    dsimp,
    erw (C.π.app j).to_add_monoid_hom.map_sum,
    refl },
  rw this,
  erw ← Profinite.pullback.condition,
  simp only [← category.assoc],
  congr' 1,
  apply Profinite.product.hom_ext,
  intros a,
  dsimp [F],
  simp only [category.assoc, Profinite.product.lift_π, Profinite.product.lift_π_assoc],
  erw (hC (c / ↑N + d)).fac (S' a) j,
  refl,
end

-- lemma gadget_cone_lift_fst_fst {J : Type u} [small_category J]
--   {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
--   (hC : ∀ a : ℝ≥0, is_limit (((level r').obj a).map_cone C))
--   (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c)
--   (S : cone (gadget_diagram C N c d t)) (i : fin N) (j : J)
--   (g : ((K.obj j).lvl (c / ↑N + d)).pow N ⟶ (((level r').obj (c / ↑N + d)).map_cone C).X) :
--   (hC (c / N + d)).lift ((cones.postcompose (gadget_diagram_fst_fst C N c d t i)).obj S) =
--     S.π.app j ≫ Profinite.pullback.fst
--       (Profinite.pullback.snd ((K.obj j).sum N _) ((K.obj j).cast_lvl _))
--       (t ≫ map_lvl (C.π.app j) c) ≫
--         Profinite.pullback.fst ((K.obj j).sum N _) ((K.obj j).cast_lvl _) ≫ g :=
-- begin
--   refine ((hC _).uniq
--     ((cones.postcompose (gadget_diagram_fst_fst.{u} C N c d t i)).obj S) _ _).symm,
--   intro j,
--   have := (hC _).fac ((cones.postcompose (gadget_diagram_fst_fst.{u} C N c d t i)).obj S),
--   simp only [functor.map_cone_π_app, cones.postcompose_obj_π,
--     nat_trans.comp_app, gadget_diagram_fst_snd_app],
--   rw Profinite.pullback.condition,
--   simp only [← category.assoc], congr' 2, ext,
-- end

def gadget_cone_is_limit {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (hC : ∀ a : ℝ≥0, is_limit (((level r').obj a).map_cone C))
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  is_limit (gadget_cone C N c d t) :=
{ lift := λ S,
    Profinite.pullback.lift _ _
      (Profinite.pullback.lift _ _
        (Profinite.product.lift _
          (λ i, (hC _).lift
            ((cones.postcompose (gadget_diagram_fst_fst C N c d t i)).obj S)))
        ((hC _).lift ((cones.postcompose (gadget_diagram_fst_snd C N c d t)).obj S))
        (gadget_cone_lift_aux _ _ _ _ _ _ _))
      (Profinite.punit.elim _)
      (by rw [Profinite.pullback.lift_snd, eq_comm, gadget_cone_lift_fst_snd]),
  fac' := λ S j, begin
    dsimp only [gadget_cone_π_app, map_gadget],
    apply Profinite.pullback.hom_ext;
      simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
        Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc],
    swap, { ext },
    apply Profinite.pullback.hom_ext;
      simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
        Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc],
    { apply Profinite.product.hom_ext, intro i,
      simp only [category.assoc, Profinite.product.lift_π, Profinite.product.lift_π_assoc],
      exact (hC _).fac ((cones.postcompose (gadget_diagram_fst_fst.{u} C N c d t i)).obj S) j, },
    { rw [gadget_cone_lift_fst_snd, Profinite.pullback.condition],
      simp only [← category.assoc], congr' 2, ext, }
  end,
  uniq' := λ S f h, begin
    apply Profinite.pullback.hom_ext;
      simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
        Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc],
    swap, { ext },
    apply Profinite.pullback.hom_ext;
      simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
        Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc],
    swap,
    { rw [Profinite.pullback.condition, gadget_cone_lift_fst_snd, ←category.assoc], congr' 1, ext },
    apply Profinite.product.hom_ext,
    intro i,
    rw [Profinite.product.lift_π],
    refine (hC (c / N + d)).uniq
      ((cones.postcompose (gadget_diagram_fst_fst.{u} C N c d t i)).obj S) _ _,
    intro j,
    dsimp,
    rw ← h,
    dsimp [gadget_cone, map_gadget],
    simp,
  end }

end ProFiltPseuNormGrpWithTinv₁

namespace lem98

open ProFiltPseuNormGrpWithTinv₁

instance (c : ℝ≥0) : preserves_limits (hom_functor.{u} r' Λ ⋙ (level r').obj c) :=
begin
  change preserves_limits (hom_functor r' Λ ⋙ to_PFPNG₁ r' ⋙ ProFiltPseuNormGrp₁.level.obj c),
  apply_instance,
end

def hom_diagram : discrete_quotient S ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
S.fintype_diagram ⋙ Lbar.Laurent_measures.{u u} r' ⋙ hom_functor r' Λ

/-- The cone over `hom_diagram` whose cone point is defeq to `Hom(Λ, Lbar S)`.
See lemma below. -/
def hom_Lbar_cone : cone (hom_diagram r' Λ S) :=
(hom_functor r' Λ).map_cone
  (limit.cone (S.fintype_diagram ⋙ Lbar.Laurent_measures.{u u} r'))

@[simp]
lemma hom_Lbar_cone_X : (hom_Lbar_cone r' Λ S ).X =
  ((hom_functor.{u} r' Λ).obj ((Lbar.functor.{u u} r').obj S)) := rfl

/-- The cone with cone point `Hom(Λ, Lbar S)_{≤ c}` is indeed a limit cone. -/
def hom_Lbar_cone_is_limit (c) : is_limit (((level r').obj c).map_cone
  (hom_Lbar_cone r' Λ S)) :=
begin
  let E := (limit.cone (S.fintype_diagram ⋙ Lbar.Laurent_measures.{u u} r')),
  change is_limit (((hom_functor.{u} r' Λ ⋙ (level r').obj c)).map_cone E),
  apply is_limit_of_preserves (hom_functor.{u} r' Λ ⋙ (level r').obj c)
    (limit.is_limit _),
  apply_instance,
end .

-- This should follow from the finite case of lem98.
lemma gadget_nonempty (N : ℕ) [fact (0 < N)] (T : discrete_quotient S)
  (c) (t) : nonempty ((gadget_diagram (hom_Lbar_cone r' Λ _) N c (d Λ N) t).obj T) :=
begin
  obtain ⟨h⟩ := lem98_finite Λ T N,
  specialize h c,
  let u : (hom_Lbar_cone r' Λ S).X ⟶ (hom_diagram r' Λ S).obj T :=
    ((hom_Lbar_cone r' Λ S).π.app T),
  let t' := t ≫ ((level r').obj c).map u,
  specialize h (t' punit.star).1 (t' punit.star).2,
  swap, apply_instance,
  obtain ⟨e,he1,he2⟩ := h,
  -- Now use `e`, `t'`, `he1` and `he2` to finish off the proof...
  refine ⟨⟨⟨⟨(_, _), _⟩, _⟩, _⟩⟩,
  { intro i, refine ⟨e i, he2 i⟩, },
  { let x := t' punit.star, exact ⟨x.1, x.2⟩, },
  { apply subtype.ext, exact he1.symm },
  { exact punit.star },
  { apply subtype.ext, refl, },
end

-- This should follow from Tychonoff and `gadget_nonempty`.
lemma key (N : ℕ) [fact (0 < N)] (c) (t) :
  nonempty (((hom_functor r' Λ).obj ((Lbar.functor.{u u} r').obj S)).gadget N c (d Λ N) t) :=
begin
  let E := gadget_cone (hom_Lbar_cone r' Λ _) N c (d Λ N) t,
  let hE : is_limit E := gadget_cone_is_limit _ _ _ _ _ _,
  swap, { intros a, apply hom_Lbar_cone_is_limit },
  let E' := Profinite.to_Top.map_cone E,
  let hE' : is_limit E' := is_limit_of_preserves _ hE,
  let G := gadget_diagram (hom_Lbar_cone r' Λ S) N c (d Λ N) t ⋙ Profinite.to_Top,
  let T : E'.X ≅ (Top.limit_cone G).X :=
    hE'.cone_point_unique_up_to_iso (Top.limit_cone_is_limit G),
  suffices : nonempty (Top.limit_cone G).X,
  { obtain ⟨a⟩ := this, exact ⟨T.inv a⟩, },
  apply_with Top.nonempty_limit_cone_of_compact_t2_cofiltered_system { instances := ff },
  { apply_instance },
  { intros, apply gadget_nonempty, },
  { intros j,
    change compact_space
      ((gadget_diagram (hom_Lbar_cone r' Λ S) N c (d Λ N) t).obj j),
    apply_instance },
  { intros j,
    change t2_space
      ((gadget_diagram (hom_Lbar_cone r' Λ S) N c (d Λ N) t).obj j),
    apply_instance },
end

/-- Lemma 9.8 of [Analytic], with somewhat restrictive universes -/
theorem main (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type u) [polyhedral_lattice Λ] (S : Profinite.{u}) (N : ℕ) [hN : fact (0 < N)] :
  pseudo_normed_group.splittable (Λ →+ (Lbar.functor.{u u} r').obj S) N (d Λ N) :=
begin
  constructor,
  intros c u hu,
  let t : Profinite.punit ⟶ ((hom_functor r' Λ).obj ((Lbar.functor.{u u} r').obj S)).lvl c :=
    Profinite.from_punit ⟨u,hu⟩,
  obtain ⟨K,hK⟩ := key r' Λ S N c t,
  rcases K with ⟨⟨⟨K₁,K₂⟩,hhK⟩,⟨⟩⟩,
  dsimp [t, Profinite.from_punit, Profinite.pullback.snd] at hK,
  dsimp at hhK,
  use (λ i, (K₁ i).1),
  split,
  { apply_fun (λ e, e.val) at hhK,
    change _ = K₂.val at hhK,
    apply_fun (λ e, e.val) at hK,
    rw hK at hhK,
    exact hhK.symm },
  { intros i,
    exact (K₁ i).2 }
end

end lem98

-- A version with less restrictive universes. But we don't need that. Who cares about universes.

-- /-- Lemma 9.8 of [Analytic] -/
-- lemma lem98 (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
--   (Λ : Type*) [polyhedral_lattice Λ] (S : Profinite) (N : ℕ) [hN : fact (0 < N)] :
--   pseudo_normed_group.splittable (Λ →+ (Lbar.functor r').obj S) N (lem98.d Λ N) :=
-- begin
--   admit
-- end

end
