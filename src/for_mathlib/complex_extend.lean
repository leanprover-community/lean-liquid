import algebra.homology.homotopy
import category_theory.abelian.basic

universes v u

noncomputable theory

open category_theory category_theory.limits

variables {ι₁ ι₂ : Type*}

namespace complex_shape

/-- An embedding `embedding c₁ c₂` between two complex shapes `ι₁` and `ι₂` is
an injection `ι₁ → ι₂` sending related vertices to related vertices. Recall that two
vertices are related in a complex shape iff the differential between them is allowed to
be nonzero. -/
structure embedding (c₁ : complex_shape ι₁) (c₂ : complex_shape ι₂) :=
(f : ι₁ → ι₂)
(r : ι₂ → option ι₁)
(eq_some : ∀ i i', r i = some i' ↔ f i' = i)
(c : ∀ ⦃i j⦄, c₁.rel i j → c₂.rel (f i) (f j))

namespace embedding

def pos_int_to_onat : ℤ → option ℕ
| (n:ℕ)  := n
| -[1+n] := none

def neg_int_to_onat : ℤ → option ℕ
| 0       := (0:ℕ)
| (n+1:ℕ) := none
| -[1+n]  := (n+1:ℕ)

def nat_up_int_up : embedding (complex_shape.up ℕ) (complex_shape.up ℤ) :=
{ f := coe,
  r := pos_int_to_onat,
  eq_some := begin
    rintro (i|i) i',
    { split; { rintro ⟨rfl⟩, refl }, },
    { split; { rintro ⟨⟩, } }
  end,
  c := by { rintro i j (rfl : _ = _), dsimp, refl } }

def nat_down_int_down : embedding (complex_shape.down ℕ) (complex_shape.down ℤ) :=
{ f := coe,
  r := pos_int_to_onat,
  eq_some := begin
    rintro (i|i) i',
    { split; { rintro ⟨rfl⟩, refl }, },
    { split; { rintro ⟨⟩, } }
  end,
  c := by { rintro i j (rfl : _ = _), dsimp, refl } }

def nat_down_int_up : embedding (complex_shape.down ℕ) (complex_shape.up ℤ) :=
{ f := -coe,
  r := neg_int_to_onat,
  eq_some := begin
    rintro ((_|i)|i) (_|i'),
    any_goals { split; { rintro ⟨⟩, } },
    any_goals { split; { rintro ⟨rfl⟩, refl }, },
  end,
  c := by { rintro i j (rfl : _ = _),
    simp only [pi.neg_apply, int.coe_nat_succ, neg_add_rev, up_rel, neg_add_cancel_comm], } }

def nat_up_int_down : embedding (complex_shape.up ℕ) (complex_shape.down ℤ) :=
{ f := -coe,
  r := neg_int_to_onat,
  eq_some := begin
    rintro ((_|i)|i) (_|i'),
    any_goals { split; { rintro ⟨⟩, } },
    any_goals { split; { rintro ⟨rfl⟩, refl }, },
  end,
  c := by { rintro i j (rfl : _ = _),
    simp only [pi.neg_apply, int.coe_nat_succ, neg_add_rev, down_rel, neg_add_cancel_comm] } }

end embedding

end complex_shape

variables {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂}
variables {C : Type*} [category C] [abelian C]

namespace homological_complex

open_locale zero_object

variables (e : c₁.embedding c₂)
variables (X Y Z : homological_complex C c₁) (f : X ⟶ Y) (g : Y ⟶ Z)

def embed.X : option ι₁ → C
| (some i) := X.X i
| none     := 0

def embed.d : Π i j, embed.X X i ⟶ embed.X X j
| (some i) (some j) := X.d i j
| (some i) none     := 0
| none     j        := 0

lemma embed.shape : ∀ (i j : option ι₁)
  (h : ∀ (i' j' : ι₁), i = some i' → j = some j' → ¬ c₁.rel i' j'),
  embed.d X i j = 0
| (some i) (some j) h := X.shape _ _ $ h i j rfl rfl
| (some i) none     h := rfl
| none     j        h := rfl

lemma embed.d_comp_d : ∀ i j k, embed.d X i j ≫ embed.d X j k = 0
| (some i) (some j) (some k) := X.d_comp_d _ _ _
| (some i) (some j) none     := comp_zero
| (some i) none     k        := comp_zero
| none     j        k        := zero_comp

def embed.obj : homological_complex C c₂ :=
{ X := embed.X X ∘ e.r,
  d := λ i j, embed.d X (e.r i) (e.r j),
  shape' := λ i j hij, embed.shape X _ _ begin
    simp only [e.eq_some],
    rintro i' j' rfl rfl h',
    exact hij (e.c h')
  end,
  d_comp_d' := λ i j k hij hjk, embed.d_comp_d X _ _ _ }

variables {X Y Z}

def embed.f : Π i, embed.X X i ⟶ embed.X Y i
| (some i) := f.f i
| none     := 0

lemma embed.comm :  ∀ i j, embed.f f i ≫ embed.d Y i j = embed.d X i j ≫ embed.f f j
| (some i) (some j) := f.comm _ _
| (some i) none     := show _ ≫ 0 = 0 ≫ 0, by simp only [comp_zero]
| none     j        := show 0 ≫ 0 = 0 ≫ _, by simp only [zero_comp]

def embed.map : embed.obj e X ⟶ embed.obj e Y :=
{ f := λ i, embed.f f _,
  comm' := λ i j hij, embed.comm f _ _ }

lemma embed.f_id : ∀ i, embed.f (𝟙 X) i = 𝟙 (embed.X X i)
| (some i) := rfl
| none     := has_zero_object.from_zero_ext _ _

lemma embed.f_comp : ∀ i, embed.f (f ≫ g) i = embed.f f i ≫ embed.f g i
| (some i) := rfl
| none     := has_zero_object.from_zero_ext _ _

def embed : homological_complex C c₁ ⥤ homological_complex C c₂ :=
{ obj := embed.obj e,
  map := λ X Y f, embed.map e f,
  map_id' := λ X, by { ext i, exact embed.f_id _ },
  map_comp' := by { intros, ext i, exact embed.f_comp f g _ } }
.

section homotopy

variables (f' : X ⟶ Y) (h : homotopy f f')

def embed_homotopy_hom : Π (i j : option ι₁), embed.X X i ⟶ embed.X Y j
| (some i) (some j) := h.hom i j
| (some i) none     := 0
| none     j        := 0

lemma embed_homotopy_zero : Π (i j : option ι₁)
  (H : ∀ (i' j' : ι₁), i = some i' → j = some j' → ¬ c₁.rel j' i'),
  embed_homotopy_hom f f' h i j = 0
| (some i) (some j) H := h.zero i j $ H _ _ rfl rfl
| (some i) none     H := rfl
| none     j        H := rfl

-- lemma embed_homotopy_comm : ∀ (i j k : option ι₁)
--   (Hij : ∀ (i' j' : ι₁), i = some i' → j = some j' → c₁.rel i' j')
--   (Hjk : ∀ (j' k' : ι₁), j = some j' → k = some k' → c₁.rel j' k'),
--   embed.f f j =
--     embed.d X j k ≫ embed_homotopy_hom f f' h k j +
--     embed_homotopy_hom f f' h j i ≫ embed.d Y i j +
--     embed.f f' j
-- | (some i) (some j) (some k) Hij Hjk := begin
--   have hij : c₁.rel i j := Hij _ _ rfl rfl,
--   have hjk : c₁.rel j k := Hjk _ _ rfl rfl,
--   have := h.comm j,
--   rw [prev_d_eq _ hij, d_next_eq _ hjk] at this,
--   exact this
-- end
-- | (some i) (some j) none Hij _ := begin
--   have hij : c₁.rel i j := Hij _ _ rfl rfl,
--   have := h.comm j,
--   rw [prev_d_eq _ hij] at this,
--   sorry
-- end
-- | none (some _) (some _) _ _ := sorry
-- | none (some _) none _ _ := sorry
-- | none none none _ _ := by { erw [zero_comp, zero_add, zero_add], refl }
-- | none none (some _) _ _ := by { erw [zero_comp, comp_zero, zero_add, zero_add], refl }
-- | (some _) none none _ _ := by { erw [zero_comp, comp_zero, zero_add, zero_add], refl }
-- | (some _) none (some _) _ _ := by { erw [zero_comp, comp_zero, zero_add, zero_add], refl }

lemma embed_homotopy_comm : ∀ (i : option ι₁) (F : Π i, embed.X X i ⟶ embed.X Y i)
  (hF : ∀ i, F (e.r i) = let F' := (λ (i j : ι₂),
    show ((embed e).obj X).X i ⟶ ((embed e).obj Y).X j, from
    embed_homotopy_hom f f' h (e.r i) (e.r j)) in (d_next i) F' + (prev_d i) F'),
  embed.f f i = F i + embed.f f' i
| (some i) F hF := begin
  convert h.comm i using 2,
  dsimp at hF, specialize hF (e.f i),
  sorry
end
| none     i' H := by ext

def embed_homotopy :
  homotopy ((embed e).map f) ((embed e).map f') :=
{ hom := λ i j, embed_homotopy_hom f f' h (e.r i) (e.r j),
  zero' := λ i j hij, embed_homotopy_zero f f' h _ _ begin
    simp only [e.eq_some],
    rintro i' j' rfl rfl h',
    exact hij (e.c h')
  end,
  comm := λ i,  begin
    sorry
  end }

end homotopy

end homological_complex

namespace chain_complex

def single₀_comp_embed_iso_single_component (X : C) : Π (i : ℤ),
  ((single₀ C ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up).obj X).X i ≅
    ((homological_complex.single C (complex_shape.up ℤ) 0).obj X).X i
| 0       := iso.refl _
| (n+1:ℕ) := iso.refl _
| -[1+n]  := iso.refl _

def single₀_comp_embed_iso_single :
  single₀ C ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up ≅
    homological_complex.single C (complex_shape.up ℤ) 0 :=
nat_iso.of_components
  (λ X, homological_complex.hom.iso_of_components
    (single₀_comp_embed_iso_single_component X)
    (by rintro ((_|i)|i) ((_|j)|j) hij; exact comp_zero.trans zero_comp.symm))
  begin
    intros X Y f,
    ext ((_|i)|i);
    refine (category.comp_id _).trans (eq.trans _ (category.id_comp _).symm);
    dsimp [homological_complex.single],
    { simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true], refl },
    { rw dif_neg, swap, dec_trivial, refl, },
    { rw dif_neg, swap, dec_trivial, refl, }
  end

end chain_complex
