import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Find
import Mathlib.Tactic.Have

/-

The proof idea here is not original to me; it's due to some
yet-unpublished work by Jem Lord, see README.md for some links.

-/

open CategoryTheory

universe v u

-- A category is univalent if the type of identifications between two
-- objects is equivalent to the type of bijections between those two
-- objects. I think the property stated below isn't exactly univalence
-- in light of the hset-ness of the category's type of objects, but
-- close enough for this proof.
class Univalent (C : Type u) [Category C] where
  univalence : (X Y : C) → (X ≅ Y) → X = Y

-- Evidence that h : A → B is a constant function
structure IsConst {A : Type u} {B : Type v} (h : A → B) where
  uval : B
  path : (a : A) → h a = uval

variable 
   {C : Type v} [Category C] [Univalent C] [Limits.HasLimits.{u} C] 
   {A B : C} (f : A ⟶ B) 

-- The type of factorizations of f
@[ext]
structure Factor (f : A ⟶ B) where
 X : C
 g : A ⟶ X
 h : X ⟶ B
 factorizes : g ≫ h = f

variable (φ : Factor f) (E : Type u)

/- 
The trivial factorization of f into f ≫ 𝟙 
-/ 
def idFac : Factor f :=
  let X : C := B
  let g : A ⟶ X := f
  let h : X ⟶ B := 𝟙 B
  { X := X, g := g, h := h, factorizes := by rw [Category.comp_id] }

/-
A type R is U-null if every function U → R is constant. This is a kind of "smallness"
measure on R. Most small types you think of --- list of nat, say --- are U-small because
the type of types is so big and parametrically coherent that you can't do anything interesting
trying to make a list of nats given a type argument.

Arguably the crucial idea of this proof is that there *is* an interesting function from
U to the set of factorizations of a morphism in a U-complete category.
-/
class Unull (R : Type u) where
  unull : (q : Type u → R) → IsConst q 

/-
This is an important construction. Given a factorization φ, and a type E, 
we output a factorization such that...
-/
def mFunc (φ : Factor f) (E : Type u) : Factor f := sorry

/-
... M(0) = (f, id) and...
-/
theorem factor_lemma_zero (φ : Factor f) : mFunc f φ PEmpty = idFac f := sorry
/-
... M(1) = φ 
-/
theorem factor_lemma_one (φ : Factor f) : mFunc f φ PUnit = φ := sorry

/-
If f is a morphism in a U-univalent U-complete category, then any function z : fact(f) → R
is constant.
-/
def factorToUnullValue (R : Type u) [Unull R] (z : Factor f → R) (φ : Factor f) :
        z φ = z (idFac f) := 
    let M : (E : Type u) → Factor f := mFunc f φ
    let compositeIsConst := Unull.unull (z ∘ M)
    let eqn : z (M PUnit) = z (M PEmpty) := 
       Trans.trans (compositeIsConst.path PUnit)
                   (symm (compositeIsConst.path PEmpty))
    let eq1 : M PUnit = φ := factor_lemma_one f φ
    let eq0 : M PEmpty = idFac f := factor_lemma_zero f φ
    by rw [eq0, eq1] at eqn; exact eqn

/-
 This is the main interesting lemma from which some particular parametricity results will follow.
-/
def factorToUnullIsConst (R : Type u) [Unull R] (z : Factor f → R) : IsConst z where
      uval := z (idFac f)
      path := factorToUnullValue f R z
