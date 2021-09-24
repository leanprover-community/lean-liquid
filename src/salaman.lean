namespace rbmap

variables {α β : Type*} {lt : α → α → Prop} [decidable_rel lt]

def union (m₁ m₂ : rbmap α β lt) : rbmap α β lt :=
m₁.fold (λ a b acc, acc.insert a b) (mk_rbmap α β lt)

end rbmap

namespace salaman

structure grid := (x y : ℤ)

namespace grid

instance : has_repr grid := ⟨λ p, "(" ++ repr p.1 ++ "," ++ repr p.2 ++ ")"⟩

instance : has_lt grid := ⟨λ p₁ p₂, p₁.y > p₂.y ∨ (p₁.y = p₂.y ∧ p₁.x < p₂.x)⟩

variables (p : grid)

/-- `p.u` is the gridpoint directly above `p` -/
def u : grid := ⟨p.x, p.y + 1⟩

/-- `p.d` is the gridpoint directly below `p` -/
def d : grid := ⟨p.x, p.y - 1⟩

/-- `p.l` is the gridpoint directly left of `p` -/
def l : grid := ⟨p.x - 1, p.y⟩

/-- `p.r` is the gridpoint directly right of `p` -/
def r : grid := ⟨p.x + 1, p.y⟩

end grid

namespace old

/-- An object in a double complex -/
structure obj :=
(name : string := "")
(coord : grid)

/-- A morphism (differential) in a double complex -/
structure hom :=
(name : string := "")
(src tgt : grid)

namespace obj

instance : has_repr obj := ⟨name⟩

variables (X : obj)

/-- The `x`-coordinate of an object in a double complex -/
def x := X.coord.x

/-- The `y`-coordinate of an object in a double complex -/
def y := X.coord.y

/-- A constructor for a morphism out of an object, going to the right -/
def right (s : string := "") : hom :=
{ name := s, src := X.coord, tgt := X.coord.r }

/-- A constructor for a morphism out of an object, going down -/
def down (s : string := "") : hom :=
{ name := s, src := X.coord, tgt := X.coord.d }

/-- Constructor for a zero object at a grid position -/
def mk_zero (p : grid) : obj := ⟨"0", p⟩

end obj

namespace hom

instance : has_repr hom := ⟨name⟩

variables (f : hom)

/-- A constructor for the source of a morphism -/
def mk_src (s : string := "") : obj :=
{ name := s, coord := f.src }

/-- A constructor for the target of a morphism -/
def mk_tgt (s : string := "") : obj :=
{ name := s, coord := f.tgt }

/-- Constructor for a zero morphism -/
def mk_zero (s t : grid) : hom := ⟨"0", s, t⟩

end hom

end old

----------------------------------------------------------------------------------------------------

-- class has_next (α : Type*) := (next : α → α)

-- def next {α : Type*} [has_next α] (a : α) := has_next.next a

-- def hor_grid := ℤ × ℤ

-- namespace hor_grid

-- instance : has_lt hor_grid := ⟨λ p q, p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 < q.1)⟩

-- def next (p : hor_grid) : hor_grid := ⟨p.1+1, p.2⟩

-- instance : has_next hor_grid := ⟨next⟩

-- end hor_grid

-- def ver_grid := ℤ × ℤ

-- namespace ver_grid

-- instance : has_lt ver_grid := ⟨λ p q, p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)⟩

-- def next (p : hor_grid) : hor_grid := ⟨p.1, p.2+1⟩

-- instance : has_next ver_grid := ⟨next⟩

-- end ver_grid

/-- The direction of a morphism -/
inductive dir
| H -- horizontal
| V -- vertical

namespace dir

-- def lt : dir → dir → Prop
-- | H H := false
-- | H V := true
-- | V H := false
-- | V V := false

-- instance : has_lt dir := ⟨lt⟩

end dir

inductive obj
| ob (p : grid) -- ordinary object
| rc (p : grid) -- receptor
| dn (p : grid) -- donor
| Hh (p : grid) -- horizontal homology
| Hv (p : grid) -- vertical homology

namespace grid

variables (p : grid)

def ob := obj.ob p
def rc := obj.rc p
def dn := obj.dn p
def Hh := obj.Hh p
def Hv := obj.Hv p

end grid

inductive hom : obj → obj → Type
| comp {p q r : obj} (f : hom p q) (g : hom q r) : hom p r
| hor (p : grid) : hom p.ob p.r.ob
| ver (p : grid) : hom p.ob p.d.ob
| in_rh (p : grid) : hom p.rc p.Hh -- intramural map `receptor   -> horizontal`
| in_rv (p : grid) : hom p.rc p.Hv -- intramural map `receptor   -> vertical`
| in_hd (p : grid) : hom p.Hh p.dn -- intramural map `horizontal -> donor`
| in_vd (p : grid) : hom p.Hv p.dn -- intramural map `vertical   -> donor`
| ex_h  (p : grid) : hom p.dn p.r.rc -- extramural map for horizontal morphism
| ex_v  (p : grid) : hom p.dn p.d.rc  -- extramural map for vertical morphism

namespace grid

variables (p : grid)

def hor := hom.hor p
def ver := hom.ver p
def in_rh := hom.in_rh p
def in_rv := hom.in_rv p
def in_hd := hom.in_hd p
def in_vd := hom.in_vd p
def ex_h  := hom.ex_h p
def ex_v  := hom.ex_v p

def ex_dh (p : grid) : hom p.dn p.d.Hh := p.ex_v.comp p.d.in_rh
def ex_hr (p : grid) : hom p.Hh p.d.rc := p.in_hd.comp p.ex_v

end grid

inductive hom.exact : Π {p q r}, hom p q → hom q r → Prop
| salamander_h1 (p : grid) : hom.exact p.ex_dh p.d.in_hd
| salamander_h2 (p : grid) : hom.exact p.in_hd p.ex_h
| salamander_h3 (p : grid) : hom.exact p.ex_h  p.r.in_rh
| salamander_h4 (p : grid) : hom.exact p.in_rh p.ex_hr

inductive obj.is_zero : obj → Prop
| hor (p : grid) : p.hor.exact p.r.hor → obj.is_zero p.r.Hh
| ver (p : grid) : p.ver.exact p.d.ver → obj.is_zero p.d.Hv

def grid.is_zero (p : grid) := p.ob.is_zero

inductive hom.is_iso : Π {s t}, hom s t → Prop
| of_zero_exact_zero {w x y z} (g : hom x y) (f : hom w x) (h : hom y z) :
    f.exact g → g.exact h → w.is_zero → z.is_zero → hom.is_iso g

lemma ex_h_is_iso {p : grid} (h : p.Hh.is_zero) (hr : p.r.Hh.is_zero) : p.ex_h.is_iso :=
hom.is_iso.of_zero_exact_zero _ _ _ (hom.exact.salamander_h2 p) (hom.exact.salamander_h3 p) h hr

lemma in_rh_is_iso_l {p : grid} (h : p.is_zero) (h' : p.d.is_zero) (H : p.d.r.Hh.is_zero) :
  p.r.in_rh.is_iso :=
hom.is_iso.of_zero_exact_zero _ _ _ (hom.exact.salamander_h3 _) (hom.exact.salamander_h4 _) _ _

-- | ex_h {p : grid} : is_zero (obj.hor p) → is_zero (obj.hor p.right) → is_iso (hom.ex_h p)
-- | ex_v {p : grid} : is_zero (obj.ver p) → is_zero (obj.ver p.down)  → is_iso (hom.ex_v p)
-- | in_rh_l {p : grid} : is_zero (obj.obj p) → is_zero (obj.obj p.down) →
--                         is_zero (obj.hor p.down.right) → is_iso (hom.in_rh p.right)
-- | in_vd_l {p : grid} : is_zero (obj.obj p) → is_zero (obj.obj p.down) →
--                         is_zero (obj.hor p.down.right) → is_iso (hom.in_vd p.right)

inductive iso : obj → obj → Type
| comp {p q r : obj} (f : iso p q) (g : iso q r) : iso p r
| hom {p q : obj} (f : hom p q) (hf : is_iso f) : iso p q
| inv {p q : obj} (f : hom p q) (hf : is_iso f) : iso q p






/-- A data structure for double complexes, consisting of a list of objects and morphisms -/
structure environment :=
(objs : rbmap grid string := mk_rbmap _ _)
(hors : rbmap grid string := mk_rbmap _ _)
(vers : rbmap grid string := mk_rbmap _ _)

namespace environment

variables (E : environment)

-- def d2_conditions {grid : Type*} [has_lt grid] [decidable_rel (@has_lt.lt grid _)] [has_next grid]
--   (homs : rbmap grid string) : list string :=
-- homs.rev_fold (λ p f acc,
-- match homs.find (next p) with
-- | (some g) := ((f ++ " ≫ " ++ g ++ " = 0") :: acc)
-- | none     := acc
-- end) []

def empty : environment := {}

def union (E₁ E₂ : environment) : environment :=
{ objs := E₁.objs.union E₂.objs,
  hors := E₁.hors.union E₂.hors,
  vers := E₁.vers.union E₂.vers }

def insert_obj (E : environment) (x : grid) (s : string) : environment :=
{ objs := E.objs.insert x s, ..E }

def insert_hor (E : environment) (x : grid) (s : string) : environment :=
{ hors := E.hors.insert x s, ..E }

def insert_ver (E : environment) (x : grid) (s : string) : environment :=
{ vers := E.vers.insert x s, ..E }

def mk_of_list_hors (p : ℕ) : environment → bool → ℕ → list string → environment
| E _  _ []     := E
| E tt q (s::t) := mk_of_list_hors (E.insert_obj ⟨p,q⟩ s) ff (q+1) t
| E ff q (s::t) := mk_of_list_hors (E.insert_hor ⟨p,q⟩ s) tt (q+1) t

def mk_of_list_vers (p : ℕ) : environment → ℕ → list string → environment
| E _ []     := E
| E q (s::t) := mk_of_list_vers (E.insert_ver ⟨p,q⟩ s) (q+1) t

def mk_of_list_aux : environment → ℕ → dir → list (list string) → environment
| E _ _     []     := E
| E p dir.H (r::l) := mk_of_list_aux (mk_of_list_hors p E true 0 r) p     dir.V l
| E p dir.V (r::l) := mk_of_list_aux (mk_of_list_vers p E      0 r) (p+1) dir.H l

def mk_of_list (l : list (list string)) : environment :=
mk_of_list_aux empty 0 dir.H l

def testE : environment :=
mk_of_list
[["A₁", "f₁", "B₁", "g₁", "C₁"],
 ["a₁",       "b₁",       "c₁"],
 ["A₂", "f₂", "B₂", "g₂", "C₂"],
 ["a₂",       "b₂",       "c₂"],
 ["A₃", "f₂", "B₃", "g₂", "C₃"]]



end environment

end salaman
