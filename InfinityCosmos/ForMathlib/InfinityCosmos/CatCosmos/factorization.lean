import Mathlib.CategoryTheory.Enriched.Limits.HasConicalPullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Unitor
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Functor.Currying
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

open CategoryTheory

structure Triangle (C : Type) [Category C] : Type where
  Left : C
  Middle : C
  Right : C
  fst : Left ⟶ Middle
  snd : Middle ⟶ Right

instance (C : Type) [Category C] : Category (Triangle C) where
  Hom X Y := (lf : X.Left ⟶ Y.Left) × (mf : X.Middle ⟶ Y.Middle) × (rf : X.Right ⟶ Y.Right) ×' (lf ≫ Y.fst = X.fst ≫ mf) ×' (mf ≫ Y.snd = X.snd ≫ rf)
  id X := by
    refine ⟨𝟙 X.Left,𝟙 X.Middle,𝟙 X.Right,?_,?_⟩
    . simp
    . simp
  comp {X Y Z} f g := by
    refine ⟨?_,?_,?_,?_,?_⟩
    . exact f.1 ≫ g.1
    . exact f.2.1 ≫ g.2.1
    . exact f.2.2.1 ≫ g.2.2.1
    . rw [<-Category.assoc,<- f.2.2.2.1,Category.assoc, Category.assoc, <-g.2.2.2.1]
    . rw [<-Category.assoc,<- f.2.2.2.2,Category.assoc, Category.assoc, <-g.2.2.2.2]
  id_comp X := by
    rcases X with ⟨lf,mf,rf,h1,h2⟩
    congr 4
    any_goals simp
  comp_id X := by
    rcases X with ⟨lf,mf,rf,h1,h2⟩
    congr 4
    any_goals simp
  assoc {W X Y Z} f g h := by
    simp
    congr 1
    any_goals simp
