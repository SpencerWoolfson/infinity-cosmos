import Mathlib.CategoryTheory.Enriched.Limits.HasConicalPullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Unitor
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Functor.Currying
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.AlgebraicTopology.Quasicategory.Nerve

noncomputable section
namespace CategoryTheory
open Bicategory

universe u v w

variable (C : Type u) [Bicategory C] [Bicategory.Strict C]

instance biCatAsCatEnriched : EnrichedCategory Cat C where
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

instance NerveLaxMonoidal : Functor.LaxMonoidal nerveFunctor.{u,v} where
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

abbrev SSetEnriched : Type u := (TransportEnrichment (nerveFunctor.{u,v}) C)

instance SSetEnrichedInst : EnrichedCategory SSet (SSetEnriched C) := by
  let ec : EnrichedCategory Cat C := biCatAsCatEnriched C
  apply @instEnrichedCategoryTransportEnrichment Cat _ _ C ec SSet _ _ (nerveFunctor) NerveLaxMonoidal

instance : Category (SSetEnriched C) := by
  simp [SSetEnriched,TransportEnrichment]
  infer_instance

instance SSetEnrichedOrdinary : EnrichedOrdinaryCategory SSet (SSetEnriched C) where
  homEquiv {X Y} := by
    refine Equiv.ofBijective ?_ ?_
    . intro f
      refine SSet.const ?_
      simp [EnrichedCategory.Hom,ComposableArrows]
      apply (Functor.const _).obj
      exact f
    . refine Function.bijective_iff_has_inverse.mpr ?_
      fconstructor
      . intro f
        rcases f with ⟨f, _⟩
        simp [EnrichedCategory.Hom,ComposableArrows,Quiver.Hom] at f
        refine (f ?_ ?_).obj ?_
        . refine Opposite.op ?_
          refine SimplexCategory.mk ?_
          exact 0
        . simp [SimplexCategory.mk,MonoidalCategoryStruct.tensorUnit,Limits.Types.terminalLimitCone]
          constructor
        . exact {val := 0, isLt := by simp}
      . fconstructor
        . simp [Function.LeftInverse,SSet.const]
        . intro x
          simp [Function.RightInverse,Function.LeftInverse,Functor.const,SSet.const]
          ext t u
          simp [EnrichedCategory.Hom,ComposableArrows.whiskerLeft]
          fapply Functor.ext
          . intro v
            simp [SimplexCategory.mk]
            sorry
          . sorry

def Functor.IsIsofibration {C D : Type} [Category C] [Category D] (F : C ⥤ D): Prop := ∀(c : C) (d : D) (φ : F.obj c ≅ d), ∃ (c' : C) (ψ : c ≅ c') (h : F.obj c' = d), F.map ψ.hom = φ.hom ≫ eqToHom h.symm

def Bicategory.IsIsofibration : MorphismProperty C := by
    simp [MorphismProperty]
    intro X Y f
    refine ∀(Z : C), ?_
    refine Functor.IsIsofibration ?_ (C := Z ⟶ X) (D := Z ⟶ Y)
    apply (Bicategory.postcomposing Z X Y).obj f

instance : PreInfinityCosmos (SSetEnriched C) where
  has_qcat_homs := by
    intro X Y
    unfold EnrichedCategory.Hom
    simp [SSetEnrichedInst,nerveFunctor,instEnrichedCategoryTransportEnrichment]
    exact Nerve.quasicategory
  homEquiv {X Y} := by
    refine Equiv.ofBijective ?_ ?_
    . intro f
      refine SSet.const ?_
      simp [EnrichedCategory.Hom,ComposableArrows]
      apply (Functor.const _).obj
      exact f
    . fconstructor
      . intro a b h
        let XX : SimplexCategoryᵒᵖ := by
          refine Opposite.op ?_
          refine SimplexCategory.mk 0
        let xx : (MonoidalCategoryStruct.tensorUnit SSet).obj XX := by
          simp [XX]
          fconstructor
        exact (Functor.congr_obj (congr_fun (congr_app h XX) xx) {val := 0, isLt := by simp})
      . refine Function.HasRightInverse.surjective ?_
        sorry
  IsIsofibration := sorry


end CategoryTheory
