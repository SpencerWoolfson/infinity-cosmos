import InfinityCosmos.BiCategoryTheory.BiCategoryLimits
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Bicategory.Functor.Lax
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax

open CategoryTheory

class Bicategory.withIsoFib (B : Type) extends Bicategory B where
  isIsoFib {x y : B} (f : x ⟶ y) : Prop
  iso_isoFib (x y : B) (f : x ⟶ y) (g : y ⟶ x) (h1 : f ≫ g ≅ 𝟙 x) (h1 : g ≫ f ≅ 𝟙 y) : isIsoFib f
  pb_stable (x y z : B) (f : x ⟶ y) (g : z ⟶ y) (h : isIsoFib f) (pb : ):
