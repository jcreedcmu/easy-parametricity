import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Find

/-

The proof idea here is not original to me; it's due to some
yet-unpublished work by Jem Lord, see README.md for some links.

-/

open CategoryTheory

universe v u


variable {C : Type u} [Category C] [Limits.HasLimits.{u} C] {A B : C} (f : A ⟶ B)

@[ext]
structure Factor where
 X : C
 g : A ⟶ X
 h : X ⟶ B
 factorizes : g ≫ h = f


/-
Lemma 1: For any factorization (g : A → X, h : X → B) = f, there exists a function
M : U → fact(f) that has
  M(0) = (f,id)
  M(1) = (g,h)
Proof:
We set
  M(E) = (d ∘ g : A → L, p : L → B)
where
- (L, p) is the "kernel E-tuple of h", i.e. the wide pullback of E copies of h : X → B
- d : X → L is the diagonal, i.e. the tuple ⟨ id_X, ⋯, id_X ⟩

Let's be precise about what we mean by this wide pullback.

A weak wide pullback is
- an object L
- projections πₑ : L → X for e ∈ E
- a "common map" p : L → B
- such that (e : E) → h ∘ πₑ = p

We say (L, p) is a wide pullback if it's terminal among weak wide pullbacks,
for the obvious notion of morphism.

There's always a diagonal weak wide pullback:
- L = X
- πₑ = id_X
- p = h : X → B
- commutativity holds.

Let's unravel this when E = 0. A weak wide pullback is an L and a map p : L → B.
The terminal one of these is p = id. The diagonal map d : X → B has to preserve the
p-components, so it is a slice morphism from h : X → B to id : B → B, so it must be h.
Therefore
  M(0) = (h ∘ g, id_B) = (f : A → B, id_B : B → B)
as required.

Let's unravel this when E = 1. A weak wide pullback is
- an object L
- a projection π : L → X
- a common map p : L → B
- such that h ∘ π = p

The terminal one of these sets L = X, π = id, p = h.
In fact this is the diagonal cone, so d = id, and
  M(1) = (id ∘ g, h)
as required.
-/

-- Given an E, gives the category that is to be the shape of the limit diagram
def DiagramShape (E : Type u) : Type u := Option E

-- These are the morphisms of our diagram category. It has E objects
-- "upstairs", and one object "downstairs", and for every upstairs object,
-- a unique morphism down to the downstairs object.
inductive dhmap {E : Type u} : (src tgt : DiagramShape E) → Type u where
  | dhid : (c : DiagramShape E) → dhmap c c
  | dhdown : (e : E) → dhmap (some e) none

open dhmap

def dhcomp {E : Type u} {X Y Z : DiagramShape E} : dhmap X Y → dhmap Y Z → dhmap X Z 
| (dhid c) , f => f
| (dhdown e) , (dhid none) => dhdown e

instance (E : Type u) : SmallCategory (DiagramShape E) where
  Hom := dhmap 
  id := dhid 
  comp := dhcomp
  comp_id := by intro _ _ f; cases f; all_goals rfl
  assoc := by intro _ _ _ _ f g h; cases f; all_goals (cases g; all_goals rfl)

def limF (E : Type u) (X B : C) (h : X ⟶ B) : (DiagramShape E) ⥤ C := 
 let dfobj : DiagramShape E → C 
 | none => B
 | some _ => X

 let dfmap {X0 X1 : DiagramShape E}: (X0 ⟶ X1) → (dfobj X0 ⟶ dfobj X1)
 | dhid c => 𝟙 (dfobj c)
 | dhdown e => h

 -- The actual diagram we want to take the limit of. It consists
 -- of one instance of the object B, and E many copies of the morphism
 -- h : X ⟶ B
 {
   obj := dfobj,
   map := dfmap,
   map_comp := by intro _ _ _ f g; cases f; rw [Category.id_comp]; rfl; cases g; rw [Category.comp_id]; rfl,
   map_id := by rw [← Pi.ext_iff]
 }

-- Definition of the function M : E → fact(f) 
-- in terms of the factorization (g, h)
noncomputable 
def Mfunc (φ : Factor f) (E : Type) : Factor f :=
 let ⟨ X, g, h, factorizes ⟩ := φ 

 let dfobj : DiagramShape E → C 
 | none => B
 | some _ => X

 let dfmap {X0 X1 : DiagramShape E}: (X0 ⟶ X1) → (dfobj X0 ⟶ dfobj X1)
 | dhid c => 𝟙 (dfobj c)
 | dhdown e => h

 -- The actual diagram we want to take the limit of. It consists
 -- of one instance of the object B, and E many copies of the morphism
 -- h : X ⟶ B
 let F : (DiagramShape E) ⥤ C := {
   obj := dfobj,
   map := dfmap,
   map_comp := by intro _ _ _ f g; cases f; rw [Category.id_comp]; rfl; cases g; rw [Category.comp_id]; rfl,
   map_id := by rw [← Pi.ext_iff]
 }

 let limcone : Limits.LimitCone F := Limits.getLimitCone F
 let cone := limcone.cone

 let L : C := limcone.cone.pt
 let p : L ⟶ B := limcone.cone.π.app none 

 let diagonalConeApp   : (tgt : DiagramShape E) → X ⟶ F.obj tgt 
 | none => h
 | some e => (𝟙 X)

 let diagonalCone : Limits.Cone F := {pt := X, π := {
    app := diagonalConeApp, 
    naturality := by intro A B f; cases f; aesop_cat; aesop_cat
 }}
 let d : X ⟶ L := limcone.isLimit.lift diagonalCone
 let dpLemma : d ≫ p = h := limcone.isLimit.fac diagonalCone none

 {
  X := L,
  g := g ≫ d,
  h := p ,
  factorizes := by rw [Category.assoc, dpLemma]; exact factorizes
 }




-- This is designed to be a relation which holds when Mfunc φ E ≅ φ' 
-- The "up to isomorphism"ness of it is crucial to make it easier
-- to state correctness. Instead of proving that 
-- Mfunc φ 0 = ⋯ 
-- Mfunc φ 1 = ⋯ 
-- and needing to do a bunch of uniqueness reasoning immediately, we'll just
-- prove that
-- Mrel φ 0 = ⋯ 
-- Mrel φ 1 = ⋯ 

def Mrel (φ : Factor f) (E : Type) (φ' : Factor f) : Prop :=
 let ⟨ X, g, h, factorizes ⟩ := φ 
 let ⟨ L, gd, p, factorizes' ⟩ := φ' 
 let d := sorry
 ∃ cone : Limits.LimitCone F ,  (g ≫ d = g)

def idFac : Factor f :=
  let X : C := B
  let g : A ⟶ X := f
  let h : X ⟶ B := 𝟙 B
  { X := X, g := g, h := h, factorizes := by rw [Category.comp_id] }

theorem factorLemmaZero (φ : Factor f) : Mfunc f φ Empty = idFac f := by
 ext
 sorry
 sorry
 sorry

theorem factorLemmaOne : (φ : Factor f) → Mfunc f φ Unit = φ 
 := sorry

def Unull (R : Type u) : Prop := Function.Bijective (λ (r : R) (_ : Type u) =>  r)

structure isConst {A B : Type u} (h : A → B) where
  uval : B
  path : (a : A) → h a = uval

/-
Lemma 2:
Suppose f is a morphism A → B and R is a U-null type
(meaning that K : R → U → R is an equivalence) and we have a function
r : fact(f) → R
Then r is a constant function.

Proof:
It suffices to show that for any factorization (g,h) of f
that r(g,h) = r(f,id).

So let a factorization g,h be given, and take M from the previous lemma.
Compose M : U → fact(f) and r : fact(f) → R
to get r ∘ M : U → R. By assumption, r ∘ M is a constant function.
But r(M(0)) = r(f,id) and r(M(1)) = r(g,h), so we're done.
-/
def mainLemma (R : Type u) (un : Unull R) (fc : Factor f → R) : isConst fc  :=
 sorry


 
