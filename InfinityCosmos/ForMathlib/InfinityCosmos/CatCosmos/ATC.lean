import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

open CategoryTheory

inductive ATC where
  | obj : ATC
  | map : ATC

inductive ATC.hom : ATC → ATC → Type where
  | id {a b : ATC}(h : a = b) : ATC.hom a b
  | toId : ATC.hom ATC.obj ATC.map
  | dom : ATC.hom ATC.map ATC.obj
  | cod : ATC.hom ATC.map ATC.obj
  
