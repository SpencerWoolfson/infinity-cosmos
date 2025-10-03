import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

open CategoryTheory


#check ObjectProperty.FullSubcategory

instance restrict (C : Type) [Category C] [MonoidalCategory C] (P : ObjectProperty C)
  (h1 : ∀(x y : C), (P x) ∧ (P y) → (P (MonoidalCategoryStruct.tensorObj x y))) (h2 : P (MonoidalCategoryStruct.tensorUnit C)) : MonoidalCategory (ObjectProperty.FullSubcategory P) where
    tensorObj x y := by
      fconstructor
      . exact (MonoidalCategoryStruct.tensorObj x.obj y.obj)
      . apply h1
        refine ⟨x.property,y.property⟩
    whiskerLeft X Y1 Y2 f := MonoidalCategoryStruct.whiskerLeft X.obj f
    whiskerRight {X1 X2} f Y :=by
      apply MonoidalCategoryStruct.whiskerRight
      exact f
    tensorUnit := by
      exact { obj := MonoidalCategoryStruct.tensorUnit C, property := h2 }
    tensor_id X1 X2 := by
      simp[CategoryStruct.id]
      exact Category.id_comp (𝟙 (MonoidalCategoryStruct.tensorObj X1.obj X2.obj))
    associator X Y Z := by
      apply?









#check SSet


-- def Term : SSet.QCat := by
--   fconstructor
--   . refine (Functor.const (C := Type) (J := SimplexCategoryᵒᵖ)).obj PUnit
--   . refine { hornFilling' := ?_ }
--     intro n i f h1 h2

--     simp [Functor.const]

universe u

#check Functor.prod

noncomputable instance : CartesianMonoidalCategory Type := by
  refine CartesianMonoidalCategory.ofChosenFiniteProducts ?_ ?_
  exact Limits.Types.terminalLimitCone
  exact fun X Y ↦ Limits.Types.binaryProductLimitCone X Y

noncomputable instance : CartesianClosed Type := by
  refine CartesianClosed.mk Type ?_
  intro X
  refine Exponentiable.mk X ?_ ?_
  . fconstructor
    fconstructor
    . intro Y
      exact X ⟶ Y
    . intro Y Z f g x
      exact f (g x)
    . intro Y
      ext f x
      simp
    . intro Y Z W f g
      ext a b
      simp
  . refine Adjunction.mkOfHomEquiv ?_
    fconstructor
    . intro Y Z
      simp [MonoidalCategoryStruct.tensorObj,CartesianMonoidalCategory.ofChosenFiniteProducts.tensorObj]
      fconstructor
      . intro f y x
        exact f ⟨x,y⟩
      . intro f p
        exact f p.2 p.1
      . simp [Function.LeftInverse]
      . simp [Function.RightInverse,Function.LeftInverse]
    . intro Y Z W f g
      ext p
      simp [MonoidalCategoryStruct.whiskerLeft]
    . intro Y Z W f g
      funext p
      simp


noncomputable instance ic : CartesianMonoidalCategory SSet := by
  apply CartesianMonoidalCategory.ofChosenFiniteProducts ?_ ?_
  . exact Limits.getLimitCone (Functor.empty SSet)
  . exact fun X Y ↦ limitConeOfTerminalAndPullbacks (Limits.pair X Y)

instance : CartesianClosed SSet := by
  refine CartesianClosed.mk SSet ?_
  intro X
  fconstructor
  . fconstructor
    fconstructor
    . intro Y
      fconstructor
      fconstructor
      . intro c
        let y := yoneda.obj c.unop
        unfold SSet at X
        unfold SimplicialObject at X
        let D := ic.tensorObj y X
        exact D ⟶ Y
      . intro n m f
        refine ↾?_
        intro t
        refine ?_ ≫ t
        refine MonoidalCategoryStruct.tensorHom ?_ ?_
        . apply yoneda.map
          exact f.unop
        . exact 𝟙 X
      . intro X
        funext a
        simp
      . intro _ _ _ _ _
        funext a
        simp
    . intro _ _ _
      simp


noncomputable instance cc : CartesianMonoidalCategory SSet := by
  exact CartesianMonoidalCategory.ofHasFiniteProducts


noncomputable instance : CartesianClosed SSet := by
  unfold SSet
  unfold SimplicialObject
  refine CartesianClosed.mk (SimplexCategoryᵒᵖ ⥤ Type) ?_
  intro X
  refine Exponentiable.mk X ?_ ?_
  apply curry.obj
  fconstructor
  fconstructor
  . intro Y
    rcases Y with ⟨Y,c⟩
    let yo := (yoneda (C := SimplexCategory)).obj c.unop
    let a := ((SSet.hasLimits.has_limits_of_shape (Discrete Limits.WalkingPair)).has_limit (Limits.pair X yo))
    let aa := (Limits.getLimitCone (Limits.pair X yo)).cone.pt
    exact aa ⟶ Y
  . intro Y Z f h
    simp
    fconstructor
    . intro W
      simp [Quiver.Hom]
      intro hh
      rcases hh
      apply?







noncomputable instance : CartesianMonoidalCategory SSet.QCat := by
  unfold SSet.QCat
  refine CartesianMonoidalCategory.ofChosenFiniteProducts ?_ ?_
  . refine { cone := ?_, isLimit := ?_ }
    . fconstructor
      . refine { obj := ?_, property := ?_ }
        . apply (Limits.terminal SSet)
        . refine { hornFilling' := ?_ }
          intro n i s h1 h2
          have sig : SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)) ⟶ ⊤_ SSet := by
            exact Limits.terminal.from (SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)))
          use sig
          exact Limits.terminal.hom_ext s ((SSet.horn (n + 2) i).ι ≫ sig)
      . simp [Functor.empty,Functor.const,Quiver.Hom]
        fconstructor
        . intro X
          rcases X
          contradiction
        . intro X
          rcases X
          contradiction
    . refine Limits.IsLimit.ofExistsUnique ?_
      intro s



noncomputable instance : CartesianClosed SSet.QCat where

def tp : Type × Type ⥤ Type where
  obj x := x.1 × x.2
  map f := by
    refine ↾?_
    intro p
    exact ⟨f.1 p.1,f.2 p.2⟩




def exp (a b : SSet.QCat) : SSet.QCat := by
  fconstructor
  . fconstructor
    fconstructor
    . intro c
      refine NatTrans ?_ ?_ (C :=  SimplexCategoryᵒᵖ) (D := Type)
      . refine Functor.prod' a.obj (yoneda.obj c.unop) ⋙ tp
      . exact b.obj
    . intro X Y f
      simp [Quiver.Hom,tp,yonedaEquiv]





instance sc (a b : SSet.QCat) : Category (a ⟶ b) where
  Hom f g := by
    let yocond : (SimplexCategoryᵒᵖ ⥤ Type) := ic.tensorObj ((yoneda (C := SimplexCategory)).obj (SimplexCategory.mk 2)) a.obj
    exact yocond ⟶ b.obj
  id f := by
    simp []
    fconstructor
    . intro X p
      simp at p


















-- instance : Bicategory SSet.QCat where
--   homCategory a b := by

--   whiskerLeft {a b c} f g h η := by
--     fconstructor
