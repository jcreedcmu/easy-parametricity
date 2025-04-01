import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.Logic.Function.Defs

/-

The proof idea here is not original to me; it's due to some
yet-unpublished work by Jem Lord, see README.md for some links.

-/

open CategoryTheory

universe v u

#check Limits.HasLimits
variable {C : Type u} [Category C] [Limits.HasLimits.{u} C] {A B : C} (f : A ⟶ B)

structure Factor where
 X : C
 g : A ⟶ X
 h : X ⟶ B
 factorizes : g ≫ h = f

#check Factor

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
def Mfunc : (φ : Factor f) → Type → Factor f 
| ⟨ X, g, h, factorizes ⟩ => sorry

def idFac : Factor f :=
  let X : C := B
  let g : A ⟶ X := f
  let h : X ⟶ B := 𝟙 B
  { X := X, g := g, h := h, factorizes := by rw [Category.comp_id] }

theorem factorLemmaZero : (φ : Factor f) → Mfunc f φ Empty = idFac f
 := sorry

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


