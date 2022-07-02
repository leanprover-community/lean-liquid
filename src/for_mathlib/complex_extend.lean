import algebra.homology.homotopy
import category_theory.abelian.basic
import for_mathlib.short_complex_functor_category
import for_mathlib.short_complex_homological_complex

universes v u

noncomputable theory

open category_theory category_theory.limits

variables {ι ι' ι₁ ι₂ : Type*}

namespace complex_shape

/-- An embedding `embedding c₁ c₂` between two complex shapes `ι₁` and `ι₂` is
an injection `ι₁ → ι₂` sending related vertices to related vertices. Recall that two
vertices are related in a complex shape iff the differential between them is allowed to
be nonzero. -/
@[nolint has_inhabited_instance]
structure embedding (c₁ : complex_shape ι₁) (c₂ : complex_shape ι₂) :=
(f : ι₁ → ι₂)
(r : ι₂ → option ι₁)
(eq_some : ∀ i₂ i₁, r i₂ = some i₁ ↔ f i₁ = i₂)
(c : ∀ ⦃i j⦄, c₁.rel i j → c₂.rel (f i) (f j))

namespace embedding

/-- extra condition which shall be useful to compare homology -/
def c_iff {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) : Prop :=
∀ (i j), c₁.rel i j ↔ c₂.rel (e.f i) (e.f j)

lemma r_f {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (i : ι₁) :
  e.r (e.f i) = some i := by rw e.eq_some

lemma r_none {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (i : ι₂)
  (hi: ¬∃ (i₁ : ι₁), i = e.f i₁) : e.r i = none :=
begin
  classical,
  by_contra hi2,
  apply hi,
  obtain ⟨j, hj⟩ := option.ne_none_iff_exists'.1 hi2,
  use j,
  rw e.eq_some at hj,
  rw hj,
end

/-- The map from `ℤ` to `option ℕ` which is `some n` on `n : ℕ : ℤ` and `none otherwise. -/
def pos_int_to_onat : ℤ → option ℕ
| (n:ℕ)  := n
| -[1+n] := none

/-- The map from `ℤ` to `option ℕ` which is `some n` on `-(n : ℕ : ℤ)` and `none otherwise. -/
def neg_int_to_onat : ℤ → option ℕ
| 0       := (0:ℕ)
| (n+1:ℕ) := none
| -[1+n]  := (n+1:ℕ)

/-- The obvious embedding from the ℕ-indexed "cohomological" complex `* → * → * → ...`
  to the corresponding ℤ-indexed complex. -/
def nat_up_int_up : embedding (complex_shape.up ℕ) (complex_shape.up ℤ) :=
{ f := coe,
  r := pos_int_to_onat,
  eq_some := begin
    rintro (i|i) i',
    { split; { rintro ⟨rfl⟩, refl }, },
    { split; { rintro ⟨⟩, } }
  end,
  c := by { rintro i j (rfl : _ = _), dsimp, refl } }

/-- The obvious embedding from the ℕ-indexed "homological" complex `* ← * ← * ← ...`
  to the corresponding ℤ-indexed homological complex. -/
def nat_down_int_down : embedding (complex_shape.down ℕ) (complex_shape.down ℤ) :=
{ f := coe,
  r := pos_int_to_onat,
  eq_some := begin
    rintro (i|i) i',
    { split; { rintro ⟨rfl⟩, refl }, },
    { split; { rintro ⟨⟩, } }
  end,
  c := by { rintro i j (rfl : _ = _), dsimp, refl } }

/-- Obvious embedding from the `ℕ`-indexed homological complex `* ← * ← * ...`
  to `ℤ`-indexed cohomological complex ` ... → * → * → ...` sending $n$ to $-n$
  on the corresponding map `ℕ → ℤ`. -/
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

lemma nat_down_int_up_c_iff : nat_down_int_up.c_iff :=
begin
  intros i j,
  split,
  { apply nat_down_int_up.c, },
  { intro hij,
    change j+1 = i,
    dsimp [nat_down_int_up] at hij,
    rw ← int.coe_nat_eq_coe_nat_iff,
    simp only [int.coe_nat_succ],
    linarith, },
end

/-- Obvious embedding from the `ℕ`-indexed cohomological complex `* → * → * ...`
  to `ℤ`-indexed homological complex ` ... ← * ← * ← ...` sending $n$ to $-n$
  on the corresponding map `ℕ → ℤ`. -/
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
variables {cι : complex_shape ι} {cι' : complex_shape ι'}

variables {𝒞 : Type*} [category 𝒞] [preadditive 𝒞] [has_zero_object 𝒞] -- reclaim category notation!

namespace homological_complex

open_locale zero_object

section embed_X_and_d_basics

/-

`embed`, not to be confused with `embedding` later on, is simply
the extension of constructions involving the index type `ι` of our complex,
to the larger type `option ι`, with `none` being sent to `zero`.

-/
variable (X : homological_complex 𝒞 cι)


/-- If `𝒞` is an abelian category,  and `(Xᵢ)ᵢ` is a `𝒞`-valued homological
complex on a complex-shape with index `ι`, then `embed.X X oi` for `oi : option ι`
is the value `Xᵢ` of `h` at `some i` (an object of `𝒞`), or `0` for `none`. -/
def embed.X : option ι → 𝒞
| (some i) := X.X i
| none     := 0

def embed.X_iso_of_none {e : option ι} (he : e = none) :
  embed.X X e ≅ 0 :=
by { rw he, refl }

def embed.X_is_zero_of_none {e : option ι} (he : e = none) :
  is_zero (embed.X X e) :=
is_zero.of_iso (category_theory.limits.is_zero_zero 𝒞) (embed.X_iso_of_none X he)

def embed.X_iso_of_some {e : option ι} {i} (he : e = some i) :
  embed.X X e ≅ X.X i :=
by { rw he, refl }

@[simp] lemma embed.X_none : embed.X X none = 0 := rfl
@[simp] lemma embed.X_some (i : ι) : embed.X X (some i) = X.X i := rfl

/-- The morphism `Xᵢ → Xⱼ` with `i j : option ι` coming from the complex `X`.
Equal to zero if either `i` or `j` is `none`.  -/
def embed.d : Π i j, embed.X X i ⟶ embed.X X j
| (some i) (some j) := X.d i j
| (some i) none     := 0
| none     j        := 0

def embed.d_of_none_src {e₁ e₂ : option ι} (he : e₁ = none) :
  embed.d X e₁ e₂ = 0 :=
by { rw he, refl }

def embed.d_of_none_tgt {e₁ e₂ : option ι} (he : e₂ = none) :
  embed.d X e₁ e₂ = 0 :=
by { rw he, cases e₁; refl }

def embed.d_of_some_of_some {e₁ e₂ : option ι} {i j}
  (h₁ : e₁ = some i) (h₂ : e₂ = some j) :
  embed.d X e₁ e₂ = (embed.X_iso_of_some X h₁).hom ≫ X.d i j ≫
    (embed.X_iso_of_some X h₂).inv :=
by { subst h₁, subst h₂, change _ = 𝟙 _ ≫ _ ≫ 𝟙 _, simpa }

@[simp] lemma embed.d_some_some (i j : ι) : embed.d X (some i) (some j) = X.d i j :=
rfl

/-- Prop-valued so probably won't break anything. To deal with zerology. -/
instance homological_complex.embed.subsingleton_to_none (c : _) : subsingleton (c ⟶ embed.X X none) :=
@unique.subsingleton _ (has_zero_object.unique_from c)

instance homological_complex.embed.subsingleton_of_none (c) : subsingleton (embed.X X none ⟶ c) :=
@unique.subsingleton _ (has_zero_object.unique_to c)

@[simp] lemma embed.d_to_none (i : option ι) : embed.d X i none = 0 :=
by cases i; refl

@[simp] lemma embed.d_of_none (i : option ι) : embed.d X none i = 0 :=
rfl

lemma embed.shape : ∀ (i j : option ι)
  (h : ∀ (i' j' : ι), i = some i' → j = some j' → ¬ cι.rel i' j'),
  embed.d X i j = 0
| (some i) (some j) h := X.shape _ _ $ h i j rfl rfl
| (some i) none     h := rfl
| none     j        h := rfl

lemma embed.d_comp_d : ∀ i j k, embed.d X i j ≫ embed.d X j k = 0
| (some i) (some j) (some k) := X.d_comp_d _ _ _
| (some i) (some j) none     := comp_zero
| (some i) none     k        := comp_zero
| none     j        k        := zero_comp

end embed_X_and_d_basics

section embedding_change_of_complex

variable (e : cι.embedding cι')

/-- Object-valued pushforward of `𝒞`-valued homological complexes along an embedding
  `ι₁ ↪ ι₂` of complex-shapes (with all indexes not in the image going to `0`). -/
def embed.obj (X : homological_complex 𝒞 cι) : homological_complex 𝒞 cι' :=
{ X := λ i, embed.X X (e.r i),
  d := λ i j, embed.d X (e.r i) (e.r j),
  shape' := λ i j hij, embed.shape X _ _ begin
    simp only [e.eq_some],
    rintro i' j' rfl rfl h',
    exact hij (e.c h')
  end,
  d_comp_d' := λ i j k hij hjk, embed.d_comp_d X _ _ _ }

variables {X Y Z : homological_complex 𝒞 cι} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Morphism-valued pushforward of `𝒞`-valued homological complexes along an embedding of complex-shapes
( with all morphisms not in the image being defined to be 0) -/
def embed.f : Π i, embed.X X i ⟶ embed.X Y i
| (some i) := f.f i
| none     := 0

@[simp] lemma embed.f_none : embed.f f none = 0 := rfl
@[simp] lemma embed.f_some (i : ι) : embed.f f (some i) = f.f i := rfl

lemma embed.f_add {f g : X ⟶ Y} : ∀ i, embed.f (f + g) i = embed.f f i + embed.f g i
| (some i) := by simp
| none     := by simp

lemma embed.comm :  ∀ i j, embed.f f i ≫ embed.d Y i j = embed.d X i j ≫ embed.f f j
| (some i) (some j) := f.comm _ _
| (some i) none     := show _ ≫ 0 = 0 ≫ 0, by simp only [comp_zero]
| none     j        := show 0 ≫ 0 = 0 ≫ _, by simp only [zero_comp]

/-- Pushforward of a morphism `(Xᵢ)ᵢ ⟶ (Yᵢ)ᵢ` of homological complexes with
  the same complex-shape `ι`, along an embedding of complex shapes c.embedding `ι → ι'` -/
def embed.map : embed.obj e X ⟶ embed.obj e Y :=
{ f := λ i, embed.f f _,
  comm' := λ i j hij, embed.comm f _ _ }

lemma embed.f_id : ∀ i, embed.f (𝟙 X) i = 𝟙 (embed.X X i)
| (some i) := rfl
| none     := has_zero_object.from_zero_ext _ _

lemma embed.f_comp : ∀ i, embed.f (f ≫ g) i = embed.f f i ≫ embed.f g i
| (some i) := rfl
| none     := has_zero_object.from_zero_ext _ _

lemma embed.f_of_some {e : option ι} {i} (he : e = some i) :
  embed.f f e =
    (embed.X_iso_of_some _ he).hom ≫
    f.f i ≫
    (embed.X_iso_of_some _ he).inv :=
by { subst he, change _ = 𝟙 _ ≫ _ ≫ 𝟙 _, simp, }

/-- Functor pushing forward, for a fixed abelian category `𝒞`, the category
of `𝒞`-valued homological complexes of shape `ι₁` along an embedding `ι₁ ↪ ι₂`
(not Lean notation -- fix somehow?) of complexes. -/
def embed : homological_complex 𝒞 cι ⥤ homological_complex 𝒞 cι' :=
{ obj := embed.obj e,
  map := λ X Y f, embed.map e f,
  map_id' := λ X, by { ext i, exact embed.f_id _ },
  map_comp' := by { intros, ext i, exact embed.f_comp f g _ } }
.

instance embed_additive :
  (embed e : homological_complex 𝒞 cι ⥤ homological_complex 𝒞 cι').additive :=
 { map_add' := λ X Y f g, by { ext, exact embed.f_add _, }, }

def embed_iso (i : ι) : ((embed e).obj X).X (e.f i) ≅ X.X i :=
eq_to_iso
begin
  delta embed embed.obj,
  dsimp,
  rw e.r_f,
  refl,
end

@[simp]
lemma embed_nat_obj_down_up_succ
  (C : chain_complex 𝒞 ℕ) (i : ℕ) :
  ((embed complex_shape.embedding.nat_down_int_up).obj C).X (-[1+i]) = C.X (i+1) := rfl

@[simp]
lemma embed_nat_obj_down_up_zero
  (C : chain_complex 𝒞 ℕ) :
  ((embed complex_shape.embedding.nat_down_int_up).obj C).X 0 = C.X 0 := rfl

@[simp]
lemma embed_nat_obj_down_up_pos
  (C : chain_complex 𝒞 ℕ) (i : ℕ) :
  ((embed complex_shape.embedding.nat_down_int_up).obj C).X (i+1) = 0 := rfl

end embedding_change_of_complex

section homotopy

variables {X Y : homological_complex 𝒞 cι}

variables (f f' : X ⟶ Y) (h : homotopy f f')

/-- The morphism `hᵢⱼ: Xᵢ ⟶ Yⱼ` coming from a homotopy between two morphisms of type `X ⟶ Y`.
  Here `X` and `Y` are complexes of shape `ι` and the indices `i j` run over `option ι`. -/
def embed_homotopy_hom : Π (i j : option ι), embed.X X i ⟶ embed.X Y j
| (some i) (some j) := h.hom i j
| (some i) none     := 0
| none     j        := 0

@[simp] lemma embed_homotopy_hom_some (i j : ι) :
  embed_homotopy_hom f f' h (some i) (some j) = h.hom i j := rfl

@[simp] lemma embed_homotopy_hom_eq_zero_of_to_none (oi : option ι) :
  embed_homotopy_hom f f' h oi none = 0 := by cases oi; refl

@[simp] lemma embed_homotopy_hom_eq_zero_of_of_none (oi : option ι) :
  embed_homotopy_hom f f' h none oi = 0 := rfl

lemma embed_homotopy_zero : Π (oi oj : option ι)
  (H : ∀ (i j : ι), oi = some i → oj = some j → ¬ cι.rel j i),
  embed_homotopy_hom f f' h oi oj = 0
| (some i) (some j) H := h.zero i j $ H _ _ rfl rfl
| (some i) none     H := rfl
| none     j        H := rfl

def embed_homotopy (e : cι.embedding cι') :
  homotopy ((embed e).map f) ((embed e).map f') :=
{ hom := λ i j, embed_homotopy_hom f f' h (e.r i) (e.r j),
  zero' := λ i j hij, embed_homotopy_zero f f' h _ _ begin
    simp only [e.eq_some],
    rintro i' j' rfl rfl h',
    exact hij (e.c h')
  end,
  comm := λ i',  begin
    by_cases hi : ∃ i : ι, i' = e.f i,
    { rcases hi with ⟨i, rfl⟩,
      have this := h.comm i,
      have h4 := e.r_f i,
      -- it's `exact this` modulo `h4`
      delta embed embed.map,
      dsimp only,
      apply_fun (λ x, (embed_iso e i).hom ≫ x ≫ (embed_iso e i).symm.hom) at this,
      convert this,
      { simp only [embed_iso, eq_to_iso.hom, iso.symm_hom, eq_to_iso.inv,
          functor.conj_eq_to_hom_iff_heq],
        rw e.r_f i,
        refl, },
      { simp only [embed_iso, eq_to_iso.hom, iso.symm_hom, eq_to_iso.inv,
          preadditive.add_comp, category.assoc, preadditive.comp_add],
        congr' 2,
        { -- next 30 lines is hacky d_next argument
          rw functor.conj_eq_to_hom_iff_heq,
          delta d_next embed.obj id_rhs embed_homotopy_hom,
          dsimp only,
          induction hi : cι.next i,
          { delta complex_shape.next option.choice at hi,
            split_ifs at hi with h1, cases hi, clear hi,
            simp only [add_monoid_hom.mk'_apply],
            simp only [nonempty_subtype, not_exists] at h1,
            induction hi' : cι'.next (e.f i),
            { simp only,
              rw ← functor.conj_eq_to_hom_iff_heq,
              { simp only [zero_comp, comp_zero] },
              { rw h4, refl },
              { rw h4, refl },
            },
            { cases val with j hj,
              rw h4,
              simp only [heq_iff_eq],
              by_cases hj' : e.r j = none,
              { rw hj', simp only [embed.d_to_none, zero_comp] },
              obtain ⟨i₁, hi₁⟩ := option.ne_none_iff_exists.1 hj',
              rw ← hi₁,
              specialize h1 i₁,
              simp [h.zero' _ _ h1] } },
          { cases val with j hj,
            have cj' : cι'.next (e.f i) = some ⟨e.f j, _⟩ :=
              cι'.next_eq_some (e.c hj),
            rw cj',
            simp only [add_monoid_hom.mk'_apply],
            rw [e.r_f j, h4],
            simp } },
        { rw functor.conj_eq_to_hom_iff_heq,
          delta prev_d embed.obj id_rhs embed_homotopy_hom,
          dsimp only,
          induction hi : cι.prev i,
          { delta complex_shape.prev option.choice at hi,
            split_ifs at hi with h1, cases hi, clear hi,
            simp only [add_monoid_hom.mk'_apply],
            simp only [nonempty_subtype, not_exists] at h1,
            induction hi' : cι'.prev (e.f i),
            { simp only,
              rw ← functor.conj_eq_to_hom_iff_heq,
              { simp only [zero_comp, comp_zero] },
              { rw h4, refl },
              { rw h4, refl },
            },
            { cases val with j hj,
              rw h4,
              simp only [heq_iff_eq],
              by_cases hj' : e.r j = none,
              { rw hj', simp only [embed.d_to_none, zero_comp] },
              obtain ⟨i₁, hi₁⟩ := option.ne_none_iff_exists.1 hj',
              rw ← hi₁,
              specialize h1 i₁,
              simp [h.zero' _ _ h1] } },
          { cases val with j hj,
            rw [cι'.prev_eq_some (e.c hj),add_monoid_hom.mk'_apply],
            simp only [add_monoid_hom.mk'_apply],
            rw [e.r_f j, h4],
            simp },
        },
        { rw [functor.conj_eq_to_hom_iff_heq, e.r_f i],
          refl, } } },
    { -- i' not in image
      have foo := e.r_none _ hi,
      suffices : subsingleton (embed.X X (e.r i') ⟶ embed.X Y (e.r i')),
      { refine @subsingleton.elim _ this _ _ },
      convert (homological_complex.embed.subsingleton_of_none X _),
    },
  end }

end homotopy

section homology_comparison

def congr_eval (𝓐 : Type*) [category 𝓐] [abelian 𝓐] (c₁ : complex_shape ι₁) (i j : ι₁)
  (h : i = j) : eval 𝓐 c₁ i ≅ eval 𝓐 c₁ j := eq_to_iso (by rw h)

def congr_prev_functor (𝓐 : Type*) [category 𝓐] [abelian 𝓐] (c₁ : complex_shape ι₁) (i j : ι₁)
  (h : i = j) : prev_functor 𝓐 c₁ i ≅ prev_functor 𝓐 c₁ j := eq_to_iso (by rw h)

def congr_next_functor (𝓐 : Type*) [category 𝓐] [abelian 𝓐] (c₁ : complex_shape ι₁) (i j : ι₁)
  (h : i = j) : next_functor 𝓐 c₁ i ≅ next_functor 𝓐 c₁ j := eq_to_iso (by rw h)

def embed_comp_eval (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (i₁ : ι₁) :
  embed e ⋙ eval 𝓐 c₂ (e.f i₁) ≅ eval 𝓐 c₁ i₁ :=
nat_iso.of_components
(λ X, embed.X_iso_of_some X (e.r_f i₁))
(λ X Y f, begin
  dsimp [embed, embed.map],
  rw embed.f_of_some f (e.r_f i₁),
  simp only [category.assoc, iso.inv_hom_id, category.comp_id],
end)

def embed_comp_prev_functor (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff) (i₁ : ι₁) :
  embed e ⋙ prev_functor 𝓐 c₂ (e.f i₁) ≅ prev_functor 𝓐 c₁ i₁ :=
begin
  rcases h₁ : c₁.prev i₁ with _ | ⟨j, hj⟩,
  { apply is_zero.iso,
    { rcases h₂ : c₂.prev (e.f i₁) with _ | ⟨k, hk⟩,
      { apply functor.is_zero_of_comp,
        exact prev_functor_is_zero _ _ _ h₂, },
      { rw is_zero.iff_id_eq_zero,
        ext X,
        apply is_zero.eq_of_src,
        dsimp,
        refine is_zero.of_iso _ (((embed e).obj X).X_prev_iso hk),
        dsimp [embed, embed.obj],
        apply embed.X_is_zero_of_none X,
        apply e.r_none,
        rintro ⟨i, hi⟩,
        rw [hi, ← he] at hk,
        rw c₁.prev_eq_some hk at h₁,
        simpa only using h₁, }, },
    { exact prev_functor_is_zero _ _ _ h₁, }, },
  { exact iso_whisker_left (embed e) (prev_functor_iso_eval 𝓐 c₂ (e.f i₁) (e.f j) (e.c hj)) ≪≫
       embed_comp_eval 𝓐 e j ≪≫
       (prev_functor_iso_eval 𝓐 c₁ i₁ j hj).symm, }
end

def embed_comp_next_functor (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff) (i₁ : ι₁) :
  embed e ⋙ next_functor 𝓐 c₂ (e.f i₁) ≅ next_functor 𝓐 c₁ i₁ :=
begin
  rcases h₁ : c₁.next i₁ with _ | ⟨j, hj⟩,
  { apply is_zero.iso,
    { rcases h₂ : c₂.next (e.f i₁) with _ | ⟨k, hk⟩,
      { apply functor.is_zero_of_comp,
        exact next_functor_is_zero _ _ _ h₂, },
      { rw is_zero.iff_id_eq_zero,
        ext X,
        apply is_zero.eq_of_src,
        dsimp,
        refine is_zero.of_iso _ (((embed e).obj X).X_next_iso hk),
        dsimp [embed, embed.obj],
        apply embed.X_is_zero_of_none X,
        apply e.r_none,
        rintro ⟨i, hi⟩,
        rw [hi, ← he] at hk,
        rw c₁.next_eq_some hk at h₁,
        simpa only using h₁,}, },
    { exact next_functor_is_zero _ _ _ h₁, }, },
  { exact iso_whisker_left (embed e) (next_functor_iso_eval 𝓐 c₂ (e.f i₁) (e.f j) (e.c hj)) ≪≫
       embed_comp_eval 𝓐 e j ≪≫
       (next_functor_iso_eval 𝓐 c₁ i₁ j hj).symm }
end

def embed_short_complex_functor_homological_complex_π₁ (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (i₂ : ι₂) (h₁₂ : e.f i₁ = i₂) :
  (embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂) ⋙ short_complex.π₁ ≅
  short_complex.functor_homological_complex 𝓐 c₁ i₁ ⋙ short_complex.π₁ :=
functor.associator _ _ _ ≪≫
  iso_whisker_left (embed e)
    (short_complex.functor_homological_complex_π₁_iso_prev_functor 𝓐 c₂ i₂) ≪≫
  (iso_whisker_left (embed e) (congr_prev_functor 𝓐 c₂ i₂ (e.f i₁) h₁₂.symm)) ≪≫
  embed_comp_prev_functor 𝓐 e he i₁ ≪≫
  (short_complex.functor_homological_complex_π₁_iso_prev_functor 𝓐 c₁ i₁).symm

def embed_short_complex_functor_homological_complex_π₂ (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (i₁ : ι₁) (i₂ : ι₂)
  (h₁₂ : e.f i₁ = i₂) :
  (embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂) ⋙ short_complex.π₂ ≅
  short_complex.functor_homological_complex 𝓐 c₁ i₁ ⋙ short_complex.π₂ :=
functor.associator _ _ _ ≪≫
  iso_whisker_left (embed e)
    (short_complex.functor_homological_complex_π₂_iso_eval 𝓐 c₂ i₂) ≪≫
  (iso_whisker_left (embed e) (congr_eval 𝓐 c₂ i₂ (e.f i₁) h₁₂.symm)) ≪≫
  embed_comp_eval 𝓐 e i₁ ≪≫
  (short_complex.functor_homological_complex_π₂_iso_eval 𝓐 c₁ i₁).symm

def embed_short_complex_functor_homological_complex_π₃ (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (i₂ : ι₂) (h₁₂ : e.f i₁ = i₂) :
  (embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂) ⋙ short_complex.π₃ ≅
  short_complex.functor_homological_complex 𝓐 c₁ i₁ ⋙ short_complex.π₃ :=
functor.associator _ _ _ ≪≫
  iso_whisker_left (embed e)
    (short_complex.functor_homological_complex_π₃_iso_next_functor 𝓐 c₂ i₂) ≪≫
  (iso_whisker_left (embed e) (congr_next_functor 𝓐 c₂ i₂ (e.f i₁) h₁₂.symm)) ≪≫
  embed_comp_next_functor 𝓐 e he i₁ ≪≫
  (short_complex.functor_homological_complex_π₃_iso_next_functor 𝓐 c₁ i₁).symm

lemma embed_d_to (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (X : homological_complex 𝓐 c₁) :
  ((embed e).obj X).d_to (e.f i₁) ≫ (embed.X_iso_of_some X (e.r_f i₁)).hom =
  (embed_comp_prev_functor 𝓐 e he i₁).hom.app X ≫ X.d_to i₁ := sorry

lemma embed_d_from (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (X : homological_complex 𝓐 c₁) :
  ((embed e).obj X).d_from (e.f i₁) ≫ (embed_comp_next_functor 𝓐 e he i₁).hom.app X =
  (embed.X_iso_of_some X (e.r_f i₁)).hom ≫ X.d_from i₁ := sorry

def embed_short_complex_functor_homological_complex (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (i₂ : ι₂) (h₁₂ : e.f i₁ = i₂) :
  embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂ ≅
  short_complex.functor_homological_complex 𝓐 c₁ i₁ :=
begin
  refine short_complex.functor_nat_iso_mk
    (embed_short_complex_functor_homological_complex_π₁ 𝓐 e he i₁ i₂ h₁₂)
    (embed_short_complex_functor_homological_complex_π₂ 𝓐 e i₁ i₂ h₁₂)
    (embed_short_complex_functor_homological_complex_π₃ 𝓐 e he i₁ i₂ h₁₂) _ _,
  { subst h₁₂,
    ext X,
    dsimp [nat_trans.hcomp, embed_short_complex_functor_homological_complex_π₂,
      short_complex.functor_homological_complex_π₂_iso_eval,
      embed_short_complex_functor_homological_complex_π₁, congr_eval,
      congr_prev_functor, embed_comp_eval, iso.refl,
      short_complex.functor_homological_complex_π₁_iso_prev_functor],
    simp only [category.assoc],
    erw [nat_trans.id_app, nat_trans.id_app],
    repeat { erw category.id_comp, },
    repeat { erw category.comp_id, },
    apply embed_d_to, },
  { subst h₁₂,
    ext X,
    dsimp [nat_trans.hcomp, embed_short_complex_functor_homological_complex_π₂,
      short_complex.functor_homological_complex_π₂_iso_eval,
      embed_short_complex_functor_homological_complex_π₃, congr_eval,
      congr_prev_functor, embed_comp_eval, iso.refl,
      short_complex.functor_homological_complex_π₃_iso_next_functor],
    simp only [category.assoc],
    erw [nat_trans.id_app, nat_trans.id_app],
    repeat { erw category.id_comp, },
    repeat { erw category.comp_id, },
    apply embed_d_from, },
end

def homology_embed_nat_iso (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
{c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (i₂ : ι₂) (h₁₂ : e.f i₁ = i₂) :
  embed e ⋙ homology_functor 𝓐 c₂ i₂ ≅ homology_functor 𝓐 c₁ i₁ :=
begin
  calc embed e ⋙ homology_functor 𝓐 c₂ i₂ ≅
    embed e ⋙ (short_complex.functor_homological_complex 𝓐 c₂ i₂ ⋙
      short_complex.homology_functor) : _
  ... ≅ (embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂) ⋙
      short_complex.homology_functor : _
  ... ≅ short_complex.functor_homological_complex 𝓐 c₁ i₁ ⋙
    short_complex.homology_functor : _
  ... ≅ homology_functor 𝓐 c₁ i₁ : _,
  { exact iso_whisker_left _ (short_complex.homology_functor_iso 𝓐 c₂ i₂), },
  { exact (functor.associator _ _ _).symm, },
  { exact iso_whisker_right
    (embed_short_complex_functor_homological_complex 𝓐 e he i₁ i₂ h₁₂) _, },
  { exact (short_complex.homology_functor_iso 𝓐 c₁ i₁).symm, },
end

end homology_comparison

end homological_complex

namespace chain_complex

def single₀_comp_embed_iso_single_component (X : 𝒞) : Π (i : ℤ),
  ((single₀ 𝒞 ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up).obj X).X i ≅
    ((homological_complex.single 𝒞 (complex_shape.up ℤ) 0).obj X).X i
| 0       := iso.refl _
| (n+1:ℕ) := iso.refl _
| -[1+n]  := iso.refl _

def single₀_comp_embed_iso_single :
  single₀ 𝒞 ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up ≅
    homological_complex.single 𝒞 (complex_shape.up ℤ) 0 :=
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
