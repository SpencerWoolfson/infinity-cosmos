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

noncomputable section
namespace CategoryTheory
open Bicategory

universe u v w

variable (C : Type u) [Bicategory.{w,v,u} C] [Bicategory.Strict C]

instance biCatAsCatEnriched : EnrichedCategory Cat.{w,v} C where
  Hom X Y := Cat.of (X ⟶ Y)
  id X := (CategoryTheory.Functor.const (ULift (ULiftHom (Discrete Unit)))).obj (𝟙 X)
  comp A B C := by
    refine CategoryTheory.uncurry.obj ?_
    apply Bicategory.precomposing
  id_comp X Y := by
    fapply Functor.ext
    . intro x
      simp [MonoidalCategoryStruct.whiskerRight,MonoidalCategoryStruct.leftUnitor,Cat.isLimitProdCone]
      simp[Limits.BinaryFan.isLimitMk,Cat.prodCone]
    . intro x y f
      simp [MonoidalCategoryStruct.whiskerRight,MonoidalCategoryStruct.leftUnitor,Cat.isLimitProdCone]
      simp[Limits.BinaryFan.isLimitMk,Cat.prodCone]
      simp [Bicategory.Strict.leftUnitor_eqToIso]
  comp_id X Y := by
    fapply Functor.ext
    . intro x
      simp [MonoidalCategoryStruct.whiskerLeft,MonoidalCategoryStruct.rightUnitor,Cat.isLimitProdCone,Limits.BinaryFan.isLimitMk,Cat.prodCone]
    . intro x y f
      simp [MonoidalCategoryStruct.whiskerLeft,MonoidalCategoryStruct.rightUnitor,Cat.isLimitProdCone]
      simp[Limits.BinaryFan.isLimitMk,Cat.prodCone,Bicategory.Strict.rightUnitor_eqToIso]
  assoc W X Y Z := by
    fapply Functor.ext
    . intro x
      simp [MonoidalCategoryStruct.tensorObj,MonoidalCategoryStruct.whiskerRight]
      simp [Cat.isLimitProdCone]
      simp [Limits.BinaryFan.isLimitMk]
      exact rfl
    . intro x y f
      simp [MonoidalCategoryStruct.whiskerRight]
      simp [MonoidalCategoryStruct.whiskerLeft,Cat.isLimitProdCone,Limits.BinaryFan.isLimitMk,Cat.prodCone]
      simp [Bicategory.Strict.associator_eqToIso]
      exact rfl

instance biCatAsCatEnrichedOrdinary : EnrichedOrdinaryCategory.{_,v,u,_} Cat.{w,v} C where
  homEquiv {X Y}:= by
    simp [MonoidalCategoryStruct.tensorUnit,Cat.chosenTerminal,Quiver.Hom]
    fconstructor
    . intro f
      exact ULift.downFunctor ⋙ ULiftHom.down ⋙ Functor.fromPUnit f
    . intro F
      exact F.obj { down := ULiftHom.objUp  { as := PUnit.unit }}
    . simp[Function.LeftInverse]
    . simp[Function.RightInverse,Function.LeftInverse]
      intro x
      simp [Functor.fromPUnit,Functor.const,Functor.comp]
      apply Functor.hext
      . intro A
        simp
        exact rfl
      . intro A B g
        simp [<- Functor.map_id]
        exact rfl
  homEquiv_comp {X Y Z : C} f g := by
    simp [MonoidalCategoryStruct.leftUnitor,Cat.chosenTerminal,Cat.of]
    fapply Functor.hext
    . intro x
      exact rfl
    . intro x y h
      rcases x with ⟨⟨x⟩⟩
      rcases y with ⟨⟨y⟩⟩
      have eq1 : x = y := by
        exact rfl
      cases eq1
      have eq2 : h = 𝟙 _ := by
        exact rfl
      rw [eq2]
      simp
      exact rfl

instance NerveLaxMonoidal : Functor.LaxMonoidal nerveFunctor.{w,v} where
  ε' := by
    fconstructor
    . intro X
      simp [MonoidalCategoryStruct.tensorUnit,Limits.Types.terminalLimitCone]
      simp [ComposableArrows]
      simp [SimplexCategory.len]
      refine homOfElement ?_
      refine (CategoryTheory.Functor.const _).obj ?_
      refine { down := ?_ }
      refine ULiftHom.objUp ?_
      refine { as := ?_ }
      exact PUnit.unit
    . intros x y f
      exact rfl
  μ' X Y := by
    fconstructor
    . intro a b
      simp [MonoidalCategoryStruct.tensorObj,CartesianMonoidalCategory.ofChosenFiniteProducts.tensorObj,Cat.prodCone]
      rcases b with ⟨x,y⟩
      simp [ComposableArrows]
      exact Functor.prod' x y
    . intros x y f
      exact rfl

abbrev SSetEnriched : Type u := (TransportEnrichment (nerveFunctor.{w,v}) C)

instance SSetEnrichedInst : EnrichedCategory SSet (SSetEnriched C) := by
  let ec : EnrichedCategory Cat C := biCatAsCatEnriched C
  apply @instEnrichedCategoryTransportEnrichment Cat _ _ C ec SSet _ _ (nerveFunctor) NerveLaxMonoidal

instance SSetEnrichedCat : Category.{v,u} (SSetEnriched C) := by
  simp [SSetEnriched,TransportEnrichment]
  infer_instance

instance SSetEnrichedOrdinary : EnrichedOrdinaryCategory.{_,v,u,_} SSet (SSetEnriched C) where
  homEquiv {X Y} := by
    simp [EnrichedCategory.Hom,ComposableArrows]
    simp [MonoidalCategoryStruct.tensorUnit,Functor.chosenTerminal,Functor.const,Limits.Types.terminalLimitCone]
    fconstructor
    . intro f
      fconstructor
      . intro x
        refine homOfElement ?_
        apply (Functor.const _).obj f
      . exact fun ⦃X_1 Y_1⦄ ↦ congrFun rfl
    . intro f
      exact (f.app (Opposite.op (SimplexCategory.mk 0)) PUnit.unit).obj {val := 0, isLt := by simp}
    . intro _
      simp [homOfElement]
    . intro x
      ext t u
      rcases x with ⟨x, xn⟩
      simp at x
      simp at xn
      let ff : (Opposite.op (SimplexCategory.mk 0)) ⟶ t := by
        fconstructor
        refine (Opposite.unop t).const (Opposite.unop (Opposite.op (SimplexCategory.mk 0))) ?_
        simp
        exact {val := 0, isLt := by simp}
      let xn' := xn ff
      simp
      rw [xn']
      simp [homOfElement,Functor.const,ComposableArrows.whiskerLeft]
      fapply Functor.ext
      . intro _
        exact rfl
      . intro _ _ _
        simp[Monotone.functor]
  homEquiv_comp {X Y Z} f g := by
    simp [EnrichedCategory.Hom,ComposableArrows]
    simp [MonoidalCategoryStruct.tensorUnit,Functor.chosenTerminal,Functor.const,Limits.Types.terminalLimitCone]
    ext t u
    simp [homOfElement]
    simp [eComp,EnrichedCategory.comp]
    simp [uncurry,precomposing,Functor.mapComposableArrows]
    fapply Functor.ext
    . intro _
      simp [nerveFunctor,Functor.LaxMonoidal.μ,Functor.LaxMonoidal.μ']
    . intro _ _ _
      simp [nerveFunctor,Functor.LaxMonoidal.μ,Functor.LaxMonoidal.μ']
