import for_mathlib.snake_lemma3
import for_mathlib.les_homology
import for_mathlib.snake_lemma_naturality

noncomputable theory

open category_theory category_theory.limits

namespace category_theory

section

local attribute [-instance] category_theory.prod

@[elab_as_eliminator]
lemma preorder_prod_induction {C D : Type*} [preorder C] [preorder D]
  {motive : Π ⦃i j : C × D⦄ (f : i ⟶ j), Prop}
  (comp : ∀ {i j k : C × D} (f : i ⟶ j) (g : j ⟶ k), motive f → motive g → motive (f ≫ g))
  (H1 : ∀ (i : C) {j k : D} (f : j ≤ k), @motive (i,j) (i,k) (hom_of_le $ ⟨le_rfl, f⟩))
  (H2 : ∀ {i j : C} (k : D) (f : i ≤ j), @motive (i,k) (j,k) (hom_of_le $ ⟨f, le_rfl⟩))
  ⦃i j : C × D⦄ (f : i ⟶ j) : motive f :=
begin
  cases i with i1 i2, cases j with j1 j2,
  convert comp _ _ (H1 i1 f.le.2) (H2 j2 f.le.1),
end

end

variables {C D : Type*} [category C] [category D]

@[elab_as_eliminator]
lemma prod_induction
  {motive : Π ⦃i j : C × D⦄ (f : i ⟶ j), Prop}
  (comp : ∀ {i j k : C × D} (f : i ⟶ j) (g : j ⟶ k), motive f → motive g → motive (f ≫ g))
  (H1 : ∀ (i : C) {j k : D} (f : j ⟶ k), @motive (i,j) (i,k) (𝟙 i, f))
  (H2 : ∀ {i j : C} (k : D) (f : i ⟶ j), @motive (i,k) (j,k) (f, 𝟙 k))
  ⦃i j : C × D⦄ (f : i ⟶ j) : motive f :=
begin
  let f1 : (i.1, i.2) ⟶ (i.1, j.2) := (𝟙 i.1, f.2),
  let f2 : (i.1, j.2) ⟶ (j.1, j.2) := (f.1, 𝟙 j.2),
  have hf : f = f1 ≫ f2,
  { ext; simp only [prod_comp_fst, prod_comp_snd, category.id_comp, category.comp_id], },
  rw hf, cases i, cases j,
  apply comp; apply_assumption,
end

@[elab_as_eliminator]
lemma fin_induction (n : ℕ)
  {motive : Π ⦃i j : fin (n+1)⦄ (f : i ≤ j), Prop}
  (id : ∀ i, motive (le_refl i))
  (comp : ∀ {i j k : fin (n+1)} (f : i ≤ j) (g : j ≤ k), motive f → motive g → motive (f.trans g : i ≤ k))
  (Hsucc : ∀ (i : fin n), @motive i.cast_succ i.succ (le_of_lt $ by { rw fin.cast_succ_lt_iff_succ_le }))
  ⦃i j : fin (n+1)⦄ (f : i ≤ j) : motive f :=
begin
  revert f,
  refine fin.induction_on j _ _; clear j,
  { intro f, have hi : i = 0, { erw eq_bot_iff, exact f }, subst i, convert id _, },
  { intros j IH f,
    obtain (hij|rfl|hij) := lt_trichotomy i j.succ,
    { rw ← fin.le_cast_succ_iff at hij,
      convert comp _ _ (IH hij) (Hsucc j), },
    { convert id _, },
    { exact (f.not_lt hij).elim } }
end

end category_theory

variables {C 𝓐 : Type*} [category C] [category 𝓐] [abelian 𝓐]

namespace homological_complex

variables {ι : Type*} {c : complex_shape ι}

local notation x `⟶[`D`]` y := D.map (snake_diagram.hom x y)

def cast_horizontal (i : fin 4) (j : fin 2) : snake_diagram := (i,j.cast_succ)
def cast_vertical (i : fin 3) (j : fin 3) : snake_diagram := (i.cast_succ,j)
def succ_horizontal (i : fin 4) (j : fin 2) : snake_diagram := (i, j.succ)
def succ_vertical (i : fin 3) (j : fin 3) : snake_diagram := (i.succ,j)
def to_succ_horizontal (i : fin 4) (j : fin 2) :
  cast_horizontal i j ⟶ succ_horizontal i j := snake_diagram.hom _ _
def to_succ_vertical ( i : fin 3) (j : fin 3) :
  cast_vertical i j ⟶ succ_vertical i j := snake_diagram.hom _ _

lemma snake_diagram_induction
  {motive : Π ⦃i j : snake_diagram⦄ (f : i ⟶ j), Prop}
  (id : ∀ i : snake_diagram, motive (𝟙 i))
  (comp : ∀ (i j k : snake_diagram) (f : i ⟶ j) (g : j ⟶ k),
    motive f → motive g → motive (f ≫ g))
  (succ_horizontal : ∀ (i : fin 4) (j : fin 2),
    motive (to_succ_horizontal i j))
  (succ_vertical : ∀ (i : fin 3) (j : fin 3),
    motive (to_succ_vertical i j)) ⦃i j : snake_diagram⦄ (f : i ⟶ j) : motive f :=
begin
  apply category_theory.preorder_prod_induction comp; clear f i j,
  { intros i,
    refine @category_theory.fin_induction 2
      (λ j k f, motive (hom_of_le $ (⟨le_refl i, f⟩ : (i,j) ≤ (i,k)))) _ _ _,
    { intros j, convert id _, },
    { intros i' j k f g hf hg, convert comp _ _ _ _ _ hf hg, },
    { intros j, convert succ_horizontal i j } },
  { intros i j k, revert i j,
    refine @category_theory.fin_induction 3
      (λ i j f, motive (hom_of_le $ (⟨f, le_refl k⟩ : (i,k) ≤ (j,k)))) _ _ _,
    { intros j, convert id _, },
    { intros i' j k f g hf hg, convert comp _ _ _ _ _ hf hg, },
    { intros i, convert succ_vertical i k } },
end

-- TODO: Make a general construction, similar to `snake_diagram.mk_functor`
def mk_snake_diagram_nat_trans
  {X Y Z : C ⥤ homological_complex 𝓐 c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (H : ∀ c i, short_exact ((f.app c).f i) ((g.app c).f i))
  {c₁ c₂ : C} (φ : c₁ ⟶ c₂) (i j : ι) (hij : c.rel i j) :
  (snake (f.app c₁) (g.app c₁) (H _) i j hij).snake_diagram ⟶
  (snake (f.app c₂) (g.app c₂) (H _) i j hij).snake_diagram :=
{ app := λ e,
  match e with
  | ⟨⟨0,_⟩,⟨0,_⟩⟩ := (homology_functor _ _ i).map (X.map φ)
  | ⟨⟨0,_⟩,⟨1,_⟩⟩ := (homology_functor _ _ i).map (Y.map φ)
  | ⟨⟨0,_⟩,⟨2,_⟩⟩ := (homology_functor _ _ i).map (Z.map φ)
  | ⟨⟨1,_⟩,⟨0,_⟩⟩ := (mod_boundaries_functor _).map (X.map φ)
  | ⟨⟨1,_⟩,⟨1,_⟩⟩ := (mod_boundaries_functor _).map (Y.map φ)
  | ⟨⟨1,_⟩,⟨2,_⟩⟩ := (mod_boundaries_functor _).map (Z.map φ)
  | ⟨⟨2,_⟩,⟨0,_⟩⟩ := (cycles_functor _ _ _).map (X.map φ)
  | ⟨⟨2,_⟩,⟨1,_⟩⟩ := (cycles_functor _ _ _).map (Y.map φ)
  | ⟨⟨2,_⟩,⟨2,_⟩⟩ := (cycles_functor _ _ _).map (Z.map φ)
  | ⟨⟨3,_⟩,⟨0,_⟩⟩ := (homology_functor _ _ j).map (X.map φ)
  | ⟨⟨3,_⟩,⟨1,_⟩⟩ := (homology_functor _ _ j).map (Y.map φ)
  | ⟨⟨3,_⟩,⟨2,_⟩⟩ := (homology_functor _ _ j).map (Z.map φ)
  | _ := 0 -- impossible case
  end,
  naturality' := begin
    apply snake_diagram_induction,
    { simp },
    { intros i j k f g h1 h2, dsimp,
      simp only [functor.map_comp, category.assoc, h2, reassoc_of h1] },
    { sorry },
    { sorry }
  end }

lemma δ_natural {X Y Z : C ⥤ homological_complex 𝓐 c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (H : ∀ c i, short_exact ((f.app c).f i) ((g.app c).f i))
  {c₁ c₂ : C} (φ : c₁ ⟶ c₂) (i j : ι) (hij : c.rel i j) :
  δ (f.app c₁) (g.app c₁) (H _) i j hij ≫ (homology_functor _ _ j).map (X.map φ) =
    (homology_functor _ _ i).map (Z.map φ) ≫ δ (f.app c₂) (g.app c₂) (H _) i j hij :=
begin
  let η := mk_snake_diagram_nat_trans f g H φ i j hij,
  apply (snake_lemma.δ_natural η _ _).symm,
end

end homological_complex
