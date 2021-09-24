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

/-- `p.up` is the gridpoint directly above `p` -/
def up : grid := ⟨p.x, p.y + 1⟩

/-- `p.down` is the gridpoint directly below `p` -/
def down : grid := ⟨p.x, p.y - 1⟩

/-- `p.left` is the gridpoint directly left of `p` -/
def left : grid := ⟨p.x - 1, p.y⟩

/-- `p.right` is the gridpoint directly right of `p` -/
def right : grid := ⟨p.x + 1, p.y⟩

end grid

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
{ name := s, src := X.coord, tgt := X.coord.right }

/-- A constructor for a morphism out of an object, going down -/
def down (s : string := "") : hom :=
{ name := s, src := X.coord, tgt := X.coord.down }

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

local attribute [instance] prod.has_lt

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

inductive obj
| obj (p : grid) -- ordinary object
| rcp (p : grid) -- receptor
| dnr (p : grid) -- donor
| hor (p : grid) -- horizontal homology
| ver (p : grid) -- vertical homology

inductive hom : obj → obj → Type
| comp {p q r : obj} (f : hom p q) (g : hom q r) : hom p r
| hor (p : grid) : hom (obj.obj p) (obj.obj p.right)
| ver (p : grid) : hom (obj.obj p) (obj.obj p.down)
| in_rh (p : grid) : hom (obj.rcp p) (obj.hor p) -- intramural map `receptor   -> horizontal`
| in_rv (p : grid) : hom (obj.rcp p) (obj.ver p) -- intramural map `receptor   -> vertical`
| in_hd (p : grid) : hom (obj.hor p) (obj.dnr p) -- intramural map `horizontal -> donor`
| in_vd (p : grid) : hom (obj.ver p) (obj.dnr p) -- intramural map `vertical   -> donor`
| ex_h  (p : grid) : hom (obj.dnr p) (obj.rcp p.right) -- extramural map for horizontal morphism
| ex_v  (p : grid) : hom (obj.dnr p) (obj.rcp p.down)  -- extramural map for vertical morphism

inductive obj.is_zero : obj → Type.
inductive hom.is_zero : Π {s t}, hom s t → Type.
inductive hom.exact : Π {p q r}, hom p q → hom q r → Type.

inductive is_iso : Π {s t}, hom s t → Type
| ex_h {p : grid} : is_zero (obj.hor p) → is_zero (obj.hor p.right) → is_iso (hom.ex_h p)
| ex_v {p : grid} : is_zero (obj.ver p) → is_zero (obj.ver p.down)  → is_iso (hom.ex_v p)
| in_rh_l {p : grid} : is_zero (obj.obj p) → is_zero (obj.obj p.down) →
                        is_zero (obj.hor p.down.right) → is_iso (hom.in_rh p.right)
| in_vd_l {p : grid} : is_zero (obj.obj p) → is_zero (obj.obj p.down) →
                        is_zero (obj.hor p.down.right) → is_iso (hom.in_vd p.right)

inductive iso : obj → obj → Type
| comp {p q r : obj} (f : iso p q) (g : iso q r) : iso p r
| hom {p q : obj} (f : hom p q) (hf : is_iso f) : iso p q
| inv {p q : obj} (f : hom p q) (hf : is_iso f) : iso q p


end environment

end salaman
