import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Find
import Mathlib.Tactic.Have
import EasyParametricity.Basic

/-

The proof idea here is not original to me; it's due to some
yet-unpublished work by Jem Lord, see README.md for some links.

-/

open CategoryTheory
open CategoryStruct renaming id → rid

universe v u

variable 
   {C : Type v} [Category C] [Univalent C] [Limits.HasLimits.{u} C] 
   {A B : C} (f : A ⟶ B) 

theorem empty_cases_is_none (x : Option PEmpty) : x = none := 
  by cases x; rfl; tauto

section diagram

 -- In this section we build up the shape of the diagram we want to take limits of.

 variable (φ : Factor f) (E : Type u)

 -- The diagram category J has E objects "upstairs", and one object "downstairs"
 def J : Type u := Option E

 -- For every upstairs object, there's a unique morphism down to the
 -- downstairs object, plus identities.
 inductive Jmor {E : Type u} : (src tgt : J E) → Type u where
   | jid : (c : J E) → Jmor c c
   | jdown : (e : E) → Jmor (some e) none

 open Jmor

 -- Composition. Pretty much what it has to be.
 def jcomp {E : Type u} {X Y Z : J E} : Jmor X Y → Jmor Y Z → Jmor X Z 
 | (jid c) , f => f
 | (jdown e) , (jid none) => jdown e

 -- J is a category
 instance (E : Type u) : SmallCategory (J E) where
   Hom := Jmor
   id := jid 
   comp := jcomp
   comp_id := by intro _ _ f; cases f; all_goals rfl
   assoc := by intro _ _ _ _ f g h; cases f; all_goals (cases g; all_goals rfl)

 -- Now we define a J-shaped category in C. It consists of one
 -- instance of the object B, and E many copies of the morphism h :
 -- X ⟶ B
 def D : J E ⥤ C := 
   let X := φ.X 
   let g := φ.g
   let h := φ.h
   let Dobj : J E → C
   | none => B
   | some _ => X
   let Dmor {X0 X1 : J E}: (X0 ⟶ X1) → (Dobj X0 ⟶ Dobj X1)
   | jid c => 𝟙 (Dobj c)
   | jdown e => h
   {
     obj := Dobj,
     map := Dmor,
     map_comp := by intro _ _ _ f g; cases f; rw [Category.id_comp]; rfl; cases g; rw [Category.comp_id]; rfl,
     map_id := by rw [← Pi.ext_iff]
   }

 -- Here we take the limit of that diagram
 noncomputable
 def limCone : Limits.LimitCone (D f φ E) := Limits.getLimitCone (D f φ E) -- unused?


 -- Here we establish that the expected data really is a limit cone for the 0-ary wide product
 def zeroLimCone : Limits.LimitCone (D f φ PEmpty) := {
   cone := { pt := B, π := {
     app := fun
       | none => 𝟙 B
       | some val => by tauto,
     naturality := by
      intro A0 B0 z; cases z; { aesop_cat }; { aesop_cat }
   } },
   isLimit := {
     lift := λ s => s.π.app none
     fac := by intros s j; rw [empty_cases_is_none j]; simp
     uniq := by intros s lift fac; sorry
   }
 }


 -- Here we establish that the expected data really is a limit cone for the 1-ary wide product
 def oneLimCone : Limits.LimitCone (D f φ PUnit) := 
--  let reflLemma (A0 : J E) : D.map (jid A0) = 𝟙 (D.obj A0) := rfl
  let D := D f φ PUnit;
  {
   cone := { pt := φ.X, π := {
     app := fun
       | none => φ.h
       | some val => 𝟙 φ.X,
     naturality := (by
        intro A0 B0 z; cases z; {
          cases A0; { 
            have h : D.map (jid none) = 𝟙 (D.obj none) := by aesop_cat;
            rw [h];
            aesop_cat
          }; {aesop_cat}}; {aesop_cat})
   } },
   isLimit := {
     lift := λ s => s.π.app (some PUnit.unit)
     fac := by 
         intros s j; simp; cases j; {
          let Q := s.pt
          let n : Q ⟶ φ.X := s.π.app (some PUnit.unit)
          let m : Q ⟶ B := s.π.app none
          have : (rid s.pt) ≫ m = n ≫ φ.h := s.π.naturality (Jmor.jdown (PUnit.unit))
          aesop_cat
         }; {simp}
     uniq := by intros s lift fac; sorry
   }
 }

end diagram

/-
Auxiliary function for mFunc, which additionally takes a specified limit cone.
-/
def mFuncCone (φ : Factor f) (E : Type u) (limCone : Limits.LimitCone (D f φ E)) : Factor f := 
 let X := φ.X 
 let g := φ.g
 let h := φ.h
 let factorizes := φ.factorizes
 open Limits in
 open Jmor in
 let J := J E
 let D : J ⥤ C := D f φ E

 let L : C := limCone.cone.pt
 let p : L ⟶ B := limCone.cone.π.app none
 -- A J-shaped cone in C to construct the "diagonal" element of the wide pullback.
 -- FIXME: factor this out of mFunc.
 let diagonalConeApp: (tgt : J) → X ⟶ D.obj tgt 
 | none => h
 | some e => (𝟙 X)

 let reflLemma (A0 : J) : D.map (jid A0) = 𝟙 (D.obj A0) := rfl

 let diagonalCone : Limits.Cone D := {pt := X, π := {
    app := diagonalConeApp, 
    naturality := by
        intro A0 B0 z; cases z
        rw [reflLemma, Functor.const_obj_map,
            Category.id_comp (diagonalConeApp A0), Category.comp_id ]
        aesop_cat
 }}
 let d : X ⟶ L := limCone.isLimit.lift diagonalCone
 let dpLemma : d ≫ p = h := limCone.isLimit.fac diagonalCone none
 {
   X := L,
   g := g ≫ d,
   h := p ,
   factorizes := by rw [Category.assoc, dpLemma]; exact factorizes
 }

/-
This is an important construction. Given a factorization φ, and a type E, 
we output a factorization such that...
-/
noncomputable
def mFunc (φ : Factor f) (E : Type u) : Factor f := 
 mFuncCone f φ E (limCone f φ E)

/-
... M(0) = (f, id) and...
-/
theorem factor_lemma_zero (φ : Factor f) : mFunc f φ PEmpty = idFac f := by
 ext
 { sorry }
 { sorry }
 { sorry }
/-
... M(1) = φ 
-/
theorem factor_lemma_one (φ : Factor f) : mFunc f φ PUnit = φ := 
 sorry

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
