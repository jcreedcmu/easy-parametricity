import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Find
import Mathlib.Tactic.Have

open CategoryTheory

universe v u

class Univalent (C : Type u) [Category C] where
  univalence : (X Y : C) → (X ≅ Y) → X = Y

structure IsConst {A : Type u} {B : Type v} (h : A → B) where
  uval : B
  path : (a : A) → h a = uval

/-

The proof idea here is not original to me; it's due to some
yet-unpublished work by Jem Lord, see README.md for some links.

-/

variable 
   {C : Type v} [Category C] [Univalent C] [Limits.HasLimits.{u} C] 
   {A B : C} (f : A ⟶ B) 


@[ext]
structure Factor where
 X : C
 g : A ⟶ X
 h : X ⟶ B
 factorizes : g ≫ h = f

variable (φ : Factor f) (E : Type u)


class Unull (R : Type u) where
  unull : Function.Bijective (λ (r : R) (_ : Type u) =>  r)

def mainLemma (R : Type u) [Unull R] (z : Factor f → R) : IsConst z :=
 sorry
