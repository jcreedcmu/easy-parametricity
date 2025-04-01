import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Category.Cat.Limit

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

def Unull (R : Type u) : Prop := sorry

structure isConst {A B : Type u} (h : A → B) where
  uval : B
  path : (a : A) → h a = uval

def mainLemma (R : Type u) (un : Unull R) (fc : Factor f → R) : isConst fc  :=
 sorry
