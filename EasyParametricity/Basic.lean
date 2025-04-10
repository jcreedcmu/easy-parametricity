import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Find

open CategoryTheory

universe v u

-- Any two limits of the same diagram are the same. This is a surrogate for
-- an assumption of univalence.
class UniqueLimits (C : Type u) [Category.{u,u} C] where
  unique_limits : (J : Type u) → [Category.{u,u} J] → (D : J ⥤ C) → 
         (A B : Limits.LimitCone D) →  A = B

-- Evidence that h : A → B is a constant function
structure IsConst {A : Type u} {B : Type v} (h : A → B) where
  uval : B
  path : (a : A) → h a = uval

variable 
   {C : Type u} [inst_cat : Category C] [Limits.HasLimits.{u} C] 
   {A B : C} (f : A ⟶ B) 

-- The type of factorizations of f
@[ext]
structure Factor (f : A ⟶ B) where
 X : C
 g : A ⟶ X
 h : X ⟶ B
 factorizes : g ≫ h = f

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
measure on R. Most small types you think of --- list of nat, say --- are U-null because
the type of types is so big and parametrically coherent that you can't do anything interesting
trying to make a list of nats given a type argument.

Arguably the crucial idea of this proof is that there *is* an interesting function from
U to the set of factorizations of a morphism in a U-complete category.
-/
class Unull (R : Type u) where
  unull : (q : Type u → R) → IsConst q 

omit [Limits.HasLimits C] in 
theorem two_limit_eq {J : Type u} [inst_cat_j : Category.{u,u} J] [uu : UniqueLimits C] (D : J ⥤ C) 
         (A B : Limits.LimitCone D) : A = B :=
  UniqueLimits.unique_limits J D A B
