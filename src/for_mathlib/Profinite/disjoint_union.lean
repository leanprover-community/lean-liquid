import topology.category.Profinite
import category_theory.limits.shapes.products

/-!

In this file we show that a finite disjoint union of profinite sets agrees with the coproduct.
*Note:* The existence of the coproduct is currently shown using some abstract nonsense.

-/

section topology
variables {α β : Type*}

lemma set.nonempty.preimage' {s : set β} (hs : s.nonempty) {f : α → β} (hf : s ⊆ set.range f) :
  (f ⁻¹' s).nonempty :=
let ⟨y, hy⟩ := hs, ⟨x, hx⟩ := hf hy in ⟨x, set.mem_preimage.2 $ hx.symm ▸ hy⟩

lemma set.image_preimage_eq' {f : α → β} {s : set β} (h : s ⊆ set.range f) : f '' (f ⁻¹' s) = s :=
(set.image_preimage_subset f s).antisymm
  (λ x hx, let ⟨y, e⟩ := h hx in ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩)

lemma is_preconnected.preimage [topological_space α] [topological_space β] {s : set β}
  (hs : is_preconnected s) {f : α → β}   (hfinj : function.injective f) (hfopen : is_open_map f)
  (hsf : s ⊆ set.range f) : is_preconnected (f ⁻¹' s) := λ u v hu hv hsuv hsu hsv,
begin
  specialize hs (f '' u) (f '' v) (hfopen u hu) (hfopen v hv) _ _ _,
  { have := set.image_subset f hsuv,
    rwa [set.image_preimage_eq' hsf, set.image_union] at this },
  { obtain ⟨x, hx1, hx2⟩ := hsu,
    exact ⟨f x, hx1, x, hx2, rfl⟩ },
  { obtain ⟨y, hy1, hy2⟩ := hsv,
    exact ⟨f y, hy1, y, hy2, rfl⟩ },
  { obtain ⟨b, hbs, hbu, hbv⟩ := hs,
    obtain ⟨a, rfl⟩ := hsf hbs,
    rw function.injective.mem_set_image hfinj at hbu hbv,
    exact ⟨a, hbs, hbu, hbv⟩ }
end

lemma is_connected.preimage [topological_space α] [topological_space β] {s : set β}
  (hs : is_connected s) {f : α → β}
  (hfinj : function.injective f) (hfopen : is_open_map f) (hsf : s ⊆ set.range f) :
  is_connected (f ⁻¹' s) :=
⟨hs.nonempty.preimage' hsf, hs.is_preconnected.preimage hfinj hfopen hsf⟩

lemma set.subset_left_of_subset_union_of_inter_right_empty {s u v : set α}
  (hsuv : s ⊆ u ∪ v) (hsv : s ∩ v = ∅) : s ⊆ u :=
λ x hxs, (hsuv hxs).elim id $ λ hxv, false.elim $ show x ∈ (∅ : set α), from hsv ▸ ⟨hxs, hxv⟩

lemma set.subset_right_of_subset_union_of_inter_left_empty {s u v : set α}
  (hsuv : s ⊆ u ∪ v) (hsv : s ∩ u = ∅) : s ⊆ v :=
λ x hxs, (hsuv hxs).elim (λ hxu, false.elim $ show x ∈ (∅ : set α), from hsv ▸ ⟨hxs, hxu⟩) id

-- lemma is_preconnected.subset_of_subset_union [topological_space α] {s u v : set α}
--   (hu : is_open u) (hv : is_open v) (huv : u ∩ v = ∅) (hsuv : s ⊆ u ∪ v) (hs : is_preconnected s) :
--   s ⊆ u ∨ s ⊆ v :=
-- begin
--   specialize hs u v hu hv hsuv,
--   by_cases hsu : (s ∩ u).nonempty,
--   { left,
--     specialize hs hsu,
--     replace hs := mt hs,
--     simp only [set.not_nonempty_iff_eq_empty, huv, set.inter_empty] at hs,
--     exact set.subset_left_of_subset_union_of_inter_right_empty hsuv (hs rfl) },
--   { right,
--     exact set.subset_right_of_subset_union_of_inter_left_empty hsuv
--       (set.not_nonempty_iff_eq_empty.mp hsu),
--   },
-- end

lemma is_preconnected.subset_left_of_subset_union_of_inter_left_nonempty [topological_space α]
  {s u v : set α} (hu : is_open u) (hv : is_open v) (huv : u ∩ v = ∅) (hsuv : s ⊆ u ∪ v)
  (hsu : (s ∩ u).nonempty) (hs : is_preconnected s) : s ⊆ u :=
set.subset_left_of_subset_union_of_inter_right_empty hsuv
begin
  by_contra hsv,
  replace hsv := set.ne_empty_iff_nonempty.1 hsv,
  obtain ⟨x, hxs, hxuv⟩ := hs u v hu hv hsuv hsu hsv,
  rwa huv at hxuv,
end

lemma is_preconnected.subset_right_of_subset_union_of_inter_right_nonempty [topological_space α]
  {s u v : set α} (hu : is_open u) (hv : is_open v) (huv : u ∩ v = ∅) (hsuv : s ⊆ u ∪ v)
  (hsv : (s ∩ v).nonempty) (hs : is_preconnected s) : s ⊆ v :=
set.subset_right_of_subset_union_of_inter_left_empty hsuv
begin
  by_contra hsu,
  replace hsu := set.ne_empty_iff_nonempty.1 hsu,
  obtain ⟨x, hxs, hxuv⟩ := hs u v hu hv hsuv hsu hsv,
  rwa huv at hxuv,
end

lemma sigma.univ (X : α → Type*) :
  (set.univ : set (Σ a, X a)) = ⋃ a, sigma.mk _ '' (set.univ : set (X a)) :=
by { ext, simp only [set.image_univ, set.mem_preimage, set.mem_Union, set.mem_univ,
  set.mem_singleton_iff, set.range_sigma_mk, exists_eq'] }

lemma clopen_range_sigma_mk {X : α → Type*} [∀ a, topological_space (X a)] {a : α} :
  is_clopen (set.range (@sigma.mk α X a)) :=
⟨open_embedding_sigma_mk.open_range, closed_embedding_sigma_mk.closed_range⟩

lemma is_open_sigma_fst_preimage {X : α → Type*} [∀ a, topological_space (X a)] (s : set α) :
  is_open (sigma.fst ⁻¹' s : set (Σ a, X a)) :=
begin
  rw is_open_sigma_iff,
  intros a,
  by_cases h : a ∈ s,
  { convert is_open_univ,
    ext x,
    simp only [h, set.mem_preimage, set.mem_univ] },
  { convert is_open_empty,
    ext x,
    simp only [h, set.mem_empty_eq, set.mem_preimage] },
end

lemma sigma.is_connected_iff {X : α → Type*} [∀ a, topological_space (X a)]
  {s : set (Σ a, X a)} :
  is_connected s ↔ ∃ (a : α) (t : set (X a)), is_connected t ∧ s = sigma.mk _ '' t :=
begin
  refine ⟨λ hs, _, _⟩,
  { obtain ⟨⟨a, x⟩, hx⟩ := hs.nonempty,
    have : s ⊆ set.range (sigma.mk a),
    { have h : set.range (sigma.mk a) = sigma.fst ⁻¹' {a}, by {ext, simp},
      rw h,
      exact is_preconnected.subset_left_of_subset_union_of_inter_left_nonempty
        (is_open_sigma_fst_preimage _) (is_open_sigma_fst_preimage {x | x ≠ a}) (by {ext, simp})
        (λ y hy, by simp [classical.em]) ⟨⟨a, x⟩, hx, rfl⟩ hs.2 },
    exact ⟨a, sigma.mk a ⁻¹' s,
      hs.preimage sigma_mk_injective is_open_map_sigma_mk this,
      (set.image_preimage_eq' this).symm⟩ },
  { rintro ⟨a, t, ht, rfl⟩,
    exact ht.image _ continuous_sigma_mk.continuous_on }
end

lemma sigma.is_preconnected_iff [hα : nonempty α] {X : α → Type*}
  [∀ a, topological_space (X a)] {s : set (Σ a, X a)} :
  is_preconnected s ↔ ∃ (a : α) (t : set (X a)), is_preconnected t ∧ s = sigma.mk _ '' t :=
begin
  refine ⟨λ hs, _, _⟩,
  { obtain rfl | h := s.eq_empty_or_nonempty,
    { exact ⟨classical.choice hα, ∅, is_preconnected_empty, (set.image_empty _).symm⟩ },
    { obtain ⟨a, t, ht, rfl⟩ := sigma.is_connected_iff.1 ⟨h, hs⟩,
      refine ⟨a, t, ht.is_preconnected, rfl⟩ } },
  { rintro ⟨a, t, ht, rfl⟩,
    exact ht.image _ continuous_sigma_mk.continuous_on }
end

lemma sum.is_connected_iff {X Y : Type*} [topological_space X] [topological_space Y]
  {s : set (X ⊕ Y)} :
  is_connected s ↔
    (∃ t, is_connected t ∧ s = sum.inl '' t) ∨ ∃ t, is_connected t ∧ s = sum.inr '' t :=
begin
  refine ⟨λ hs, _, _⟩,
  { obtain ⟨x | x, hx⟩ := hs.nonempty,
    { refine or.inl ⟨sum.inl ⁻¹' s, _, _⟩,
      sorry,
      sorry },
    { refine or.inr ⟨sum.inr ⁻¹' s, _, _⟩,
      sorry,
      sorry } },
  { rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩),
    { exact ht.image _ continuous_inl.continuous_on },
    { exact ht.image _ continuous_inr.continuous_on } }
end

lemma sum.is_preconnected_iff {X Y : Type*} [topological_space X] [topological_space Y]
  {s : set (X ⊕ Y)} :
  is_preconnected s ↔
    (∃ t, is_preconnected t ∧ s = sum.inl '' t) ∨ ∃ t, is_preconnected t ∧ s = sum.inr '' t :=
begin
  refine ⟨λ hs, _, _⟩,
  { obtain rfl | h := s.eq_empty_or_nonempty,
    { exact or.inl ⟨∅, is_preconnected_empty, (set.image_empty _).symm⟩ },
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := sum.is_connected_iff.1 ⟨h, hs⟩,
    { exact or.inl ⟨t, ht.is_preconnected, rfl⟩ },
    { exact or.inr ⟨t, ht.is_preconnected, rfl⟩ } },
  { rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩),
    { exact ht.image _ continuous_inl.continuous_on },
    { exact ht.image _ continuous_inr.continuous_on } }
end

instance {α : Type*} [fintype α] (X : α → Type*) [∀ a, topological_space (X a)]
  [∀ a, compact_space (X a)] : compact_space (Σ a, X a) :=
begin
  refine ⟨_⟩,
  rw sigma.univ,
  exact compact_Union (λ i, compact_univ.image continuous_sigma_mk),
end

instance {α : Type*} [fintype α] (X : α → Type*) [∀ a, topological_space (X a)]
  [∀ a, totally_disconnected_space (X a)] :
  totally_disconnected_space (Σ a, X a) :=
begin
  refine ⟨λ s _ hs, _⟩,
  obtain rfl | h := s.eq_empty_or_nonempty,
  { exact set.subsingleton_empty },
  { obtain ⟨a, t, ht, rfl⟩ := sigma.is_connected_iff.1 ⟨h, hs⟩,
    exact ht.is_preconnected.subsingleton.image _ }
end

instance {X Y : Type*} [topological_space X] [topological_space Y]
  [totally_disconnected_space X] [totally_disconnected_space Y] :
  totally_disconnected_space (X ⊕ Y) :=
begin
  refine ⟨λ s _ hs, _⟩,
  obtain (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) := sum.is_preconnected_iff.1 hs,
  { exact ht.subsingleton.image _ },
  { exact ht.subsingleton.image _ }
end

end topology

namespace Profinite

universe u
variables {α : Type u} [fintype α] (X : α → Profinite.{u})

def empty : Profinite.{u} := Profinite.of pempty
def empty.elim (X : Profinite.{u}) : empty ⟶ X :=  { to_fun := pempty.elim }

def sum (X Y : Profinite.{u}) : Profinite.{u} :=
Profinite.of $ X ⊕ Y

def sum.inl (X Y : Profinite.{u}) : X ⟶ sum X Y :=
{ to_fun := _root_.sum.inl }

def sum.inr (X Y : Profinite.{u}) : Y ⟶ sum X Y :=
{ to_fun := _root_.sum.inr }

def sum.desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) : sum X Y ⟶ Z :=
{ to_fun := λ x, _root_.sum.rec_on x f g,
  continuous_to_fun := begin
    apply continuous_sup_dom,
    { apply continuous_coinduced_dom, exact f.continuous },
    { apply continuous_coinduced_dom, exact g.continuous }
  end }

@[simp]
lemma sum.inl_desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) :
  sum.inl X Y ≫ sum.desc X Y f g = f := by { ext, refl }

@[simp]
lemma sum.inr_desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) :
  sum.inr X Y ≫ sum.desc X Y f g = g := by { ext, refl }

lemma sum.hom_ext {Z} (X Y : Profinite.{u}) (e₁ e₂ : sum X Y ⟶ Z)
  (hl : sum.inl X Y ≫ e₁ = sum.inl X Y ≫ e₂) (hr : sum.inr X Y ≫ e₁ = sum.inr X Y ≫ e₂) :
  e₁ = e₂ :=
begin
  ext (u|u),
  { apply_fun (λ e, e u) at hl, exact hl },
  { apply_fun (λ e, e u) at hr, exact hr },
end

def sigma : Profinite.{u} :=
Profinite.of $ Σ a, X a

def sigma.ι (a : α) : X a ⟶ sigma X :=
{ to_fun := λ t, ⟨_,t⟩,
  continuous_to_fun := begin
    apply continuous_Sup_rng,
    exact ⟨a,rfl⟩,
    apply continuous_coinduced_rng,
  end }

lemma sigma.ι_injective (a : α) : function.injective (sigma.ι X a) :=
by { dsimp [sigma.ι], exact sigma_mk_injective }

lemma sigma.ι_jointly_surjective (t : sigma X) : ∃ a (x : X a), sigma.ι X a x = t :=
by { rcases t with ⟨a,t⟩, exact ⟨a,t,rfl⟩ }

def sigma.desc {Y} (f : Π a, X a ⟶ Y) : sigma X ⟶ Y :=
{ to_fun := λ ⟨a,t⟩, f a t,
  continuous_to_fun := begin
    apply continuous_Sup_dom,
    rintros _ ⟨a,rfl⟩,
    resetI,
    apply continuous_coinduced_dom,
    exact (f a).continuous
  end }

lemma sigma.desc_surjective {Y} (f : Π a, X a ⟶ Y) (surj : ∀ y, ∃ a (x : X a), f a x = y) :
  function.surjective (sigma.desc X f) :=
begin
  intros y,
  obtain ⟨a,x,hx⟩ := surj y,
  exact ⟨⟨a,x⟩,hx⟩,
end

@[simp, reassoc]
lemma sigma.ι_desc {Y} (a) (f : Π a, X a ⟶ Y) : sigma.ι X a ≫ sigma.desc X f = f a :=
by { ext, refl }

lemma sigma.hom_ext {Y} (f g : sigma X ⟶ Y) (w : ∀ a, sigma.ι X a ≫ f = sigma.ι X a ≫ g) :
  f = g :=
begin
  ext ⟨a,t⟩,
  specialize w a,
  apply_fun (λ e, e t) at w,
  exact w,
end

open category_theory

def sigma_cofan : limits.cofan X :=
limits.cofan.mk (sigma X) (sigma.ι X)

def sigma_cofan_is_colimit : limits.is_colimit (sigma_cofan X) :=
{ desc := λ S, sigma.desc _ $ λ a, S.ι.app a,
  uniq' := begin
    intros S m h,
    apply sigma.hom_ext,
    intros a,
    convert h a,
    simp,
  end }

def pullback {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) : Profinite :=
{ to_CompHaus :=
  { to_Top := Top.of { a : X × Y | f a.1 = g a.2 },
    is_compact := begin
      erw ← is_compact_iff_compact_space,
      apply is_closed.is_compact,
      apply is_closed_eq,
      all_goals { continuity },
    end,
    is_hausdorff := begin
      change t2_space { a : X × Y | f a.1 = g a.2 },
      apply_instance
    end },
  is_totally_disconnected := subtype.totally_disconnected_space }

def pullback.fst {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  pullback f g ⟶ X := { to_fun := λ a, a.1.1 }

def pullback.snd {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  pullback f g ⟶ Y := { to_fun := λ a, a.1.2 }

lemma pullback.condition {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  pullback.fst f g ≫ f = pullback.snd f g ≫ g := by { ext ⟨t,ht⟩, exact ht }

def pullback.lift {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)
  (e₁ : W ⟶ X) (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) : W ⟶ pullback f g :=
{ to_fun := λ t, ⟨(e₁ t, e₂ t), by { apply_fun (λ ee, ee t) at w, exact w }⟩ }

@[simp, reassoc]
lemma pullback.lift_fst {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)
  (e₁ : W ⟶ X) (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) :
  pullback.lift f g e₁ e₂ w ≫ pullback.fst f g = e₁ := by { ext, refl }

@[simp, reassoc]
lemma pullback.lift_snd {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)
  (e₁ : W ⟶ X) (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) :
  pullback.lift f g e₁ e₂ w ≫ pullback.snd f g = e₂ := by { ext, refl }

lemma pullback.hom_ext {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e₁ e₂ : W ⟶ pullback f g)
  (w₁ : e₁ ≫ pullback.fst f g = e₂ ≫ pullback.fst f g)
  (w₂ : e₁ ≫ pullback.snd f g = e₂ ≫ pullback.snd f g) : e₁ = e₂ :=
begin
  ext t,
  { apply_fun (λ e, e t) at w₁, exact w₁ },
  { apply_fun (λ e, e t) at w₂, exact w₂ },
end

def sigma_pullback_to_pullback_sigma {B} (f : Π a, X a ⟶ B) :
  sigma (λ a : α × α, pullback (f a.1) (f a.2)) ⟶ pullback (sigma.desc X f) (sigma.desc X f) :=
sigma.desc _ $ λ a, pullback.lift _ _
  (pullback.fst _ _ ≫ sigma.ι _ _) (pullback.snd _ _ ≫ sigma.ι _ _) begin
    cases a, dsimp at *, ext1, cases x, assumption,
  end

instance {B} (f : Π a, X a ⟶ B) : is_iso (sigma_pullback_to_pullback_sigma X f) :=
is_iso_of_bijective _
begin
  split,
  { rintros ⟨⟨a,b⟩,⟨⟨x₁,x₂⟩,hx⟩⟩ ⟨⟨a',b'⟩,⟨⟨x'₁,x'₂⟩,hx'⟩⟩ h,
    dsimp [sigma_pullback_to_pullback_sigma, sigma.desc, pullback.lift,
      sigma.ι, pullback.fst, pullback.snd] at *,
    tidy },
  { rintros ⟨⟨⟨a,x⟩,⟨b,y⟩⟩,h⟩,
    refine ⟨⟨⟨a,b⟩,⟨⟨x,y⟩,h⟩⟩,rfl⟩ }
end

@[simp]
lemma sigma_pullback_to_pullback_sigma_fst {B} (f : Π a, X a ⟶ B) :
  sigma_pullback_to_pullback_sigma X f ≫ pullback.fst _ _ =
  sigma.desc _ (λ a, pullback.fst _ _ ≫ sigma.ι _ a.1) := by ext ⟨_,_⟩; refl

@[simp]
lemma sigma_pullback_to_pullback_sigma_snd {B} (f : Π a, X a ⟶ B) :
  sigma_pullback_to_pullback_sigma X f ≫ pullback.snd _ _ =
  sigma.desc _ (λ a, pullback.snd _ _ ≫ sigma.ι _ a.2) := by ext ⟨_,_⟩; refl

--TODO: Finish off the api for the explicit pullback

def equalizer {X Y : Profinite.{u}} (f g : X ⟶ Y) : Profinite :=
{ to_CompHaus :=
  { to_Top := Top.of { x | f x = g x },
    is_compact := begin
      erw ← is_compact_iff_compact_space,
      apply is_closed.is_compact,
      apply is_closed_eq,
      exact f.continuous,
      exact g.continuous
    end,
    is_hausdorff := begin
      change t2_space { x | f x = g x },
      apply_instance
    end },
  is_totally_disconnected := subtype.totally_disconnected_space }

def equalizer.ι {X Y : Profinite.{u}} (f g : X ⟶ Y) : equalizer f g ⟶ X := { to_fun := λ x, x.1 }

def equalizer.lift {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e : W ⟶ X) (w : e ≫ f = e ≫ g) :
  W ⟶ equalizer f g :=
{ to_fun := λ t, ⟨e t, by { apply_fun (λ ee, ee t) at w, exact w }⟩ }

@[simp, reassoc]
def equalizer.lift_ι {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e : W ⟶ X)
  (w : e ≫ f = e ≫ g) : equalizer.lift f g e w ≫ equalizer.ι f g = e := by { ext, refl }

def equalizer.hom_ext {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e₁ e₂ : W ⟶ equalizer f g)
  (w : e₁ ≫ equalizer.ι f g = e₂ ≫ equalizer.ι f g) : e₁ = e₂ :=
begin
  ext t,
  apply_fun (λ ee, ee t) at w,
  exact w,
end

end Profinite
