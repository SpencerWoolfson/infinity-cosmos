import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Closed.Cartesian


open CategoryTheory

universe u

noncomputable section

instance : Limits.HasBinaryProducts SSet.QCat.{u} := by
  apply Limits.hasLimitsOfShape_of_closedUnderLimits
  intro F c hc j
  fconstructor
  intro n i σ0 h1 h2
  let Jl := j {as := (Limits.WalkingPair.left)}
  rcases Jl with ⟨Jl⟩
  let Jl' := Jl (σ0 ≫ (c.π.app {as := (Limits.WalkingPair.left)})) h1 h2
  let Jr := j {as := (Limits.WalkingPair.right)}
  rcases Jr with ⟨Jr⟩
  let Jr' := Jr (σ0 ≫ (c.π.app {as := (Limits.WalkingPair.right)})) h1 h2
  fconstructor
  . apply _ ≫ hc.lift ?_
    . fconstructor
      . exact SSet.stdSimplex.obj (SimplexCategory.mk (n + 2))
      . refine Limits.mapPair  (Exists.choose (Jl')) (Exists.choose (Jr'))
    . exact 𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)))
  . apply (Limits.IsLimit.hom_ext hc)
    . intro t
      rcases t with ⟨t⟩
      cases t
      . simp [<- Exists.choose_spec Jl']
      . simp [<- Exists.choose_spec Jr']

/- This could be made shorter for sure -/
instance : Limits.HasTerminal SSet.QCat.{u} := by
  apply Limits.hasLimitsOfShape_of_closedUnderLimits
  intro F c hc j
  fconstructor
  intro n i σ0 h1 h2
  fconstructor
  . let ss' : Limits.Cone F := by
      fconstructor
      . exact SSet.stdSimplex.obj (SimplexCategory.mk (n + 2))
      . refine Discrete.natTrans ?_
        intro emp
        rcases emp
        contradiction
    refine ?_ ≫ (hc.lift ss')
    . simp [ss']
      exact 𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)))
  . simp
    let σ0Lift : Limits.Cone F := by
      fconstructor
      . exact (SSet.horn (n + 2) i).toSSet
      . refine Discrete.natTrans ?_
        intro emp
        rcases emp
        contradiction
    let σ0isLift : σ0 = hc.lift σ0Lift := by
      apply hc.uniq σ0Lift σ0
      intro emp
      rcases emp
      contradiction
    rw [σ0isLift]
    set s : (SSet.horn (n + 2) i).toSSet ⟶ c.pt := (SSet.horn (n + 2) i).ι ≫ hc.lift { pt := SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)), π := Discrete.natTrans fun emp ↦ _ }
    let sisLift : s = hc.lift σ0Lift := by
      apply hc.uniq σ0Lift s
      intro emp
      rcases emp
      contradiction
    rw [sisLift]

instance SSet.CartesianMonoidal : BraidedCategory SSet := by
  exact BraidedCategory.ofCartesianMonoidalCategory

instance QCat.HasFiniteProducts : Limits.HasFiniteProducts SSet.QCat.{u} := by
  exact hasFiniteProducts_of_has_binary_and_terminal


instance QCat.CartesianMonoidal : CartesianMonoidalCategory SSet.QCat.{u} := by
  apply CartesianMonoidalCategory.ofChosenFiniteProducts
  . exact Limits.getLimitCone (Functor.empty SSet.QCat)
  . exact fun X Y ↦ Limits.getLimitCone (Limits.pair X Y)

instance QCat.Monoidal : MonoidalCategory SSet.QCat.{u} := by
  exact CartesianMonoidal.toMonoidalCategory

-- instance QCat.CartesianClosed : CartesianClosed SSet.QCat.{u} := by
--   refine CartesianClosed.mk SSet.QCat ?_
--   intro X
--   refine Exponentiable.mk X ?_ ?_
--   .

instance SSet.CartesianClosed : CartesianClosed SSet.{u} := by
  unfold SSet SimplicialObject
  exact FunctorToTypes.monoidalClosed

#check MonoidalClosed

def QCat.InternalHom (X : SSet) (Y : SSet.QCat.{u}) : SSet.QCat.{u} := by
  fconstructor
  . exact (SSet.CartesianClosed.closed X).rightAdj.obj Y.obj
  . fconstructor
    intro n i σ0 h1 h2
    fconstructor
    . refine ((SSet.CartesianClosed.closed X).adj.homEquiv _ Y.obj).toFun ?_
      refine (BraidedCategory.braiding X (SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)))).hom ≫ ?_
      refine ((SSet.CartesianClosed.closed _).adj.homEquiv _ Y.obj).invFun ?_
      let step1 := ((SSet.CartesianClosed.closed _).adj.homEquiv _ Y.obj).invFun σ0
      let step2 := (BraidedCategory.braiding (SSet.horn (n + 2) i).toSSet X ).hom ≫ step1
      let step3 := ((SSet.CartesianClosed.closed _).adj.homEquiv _ Y.obj).toFun step2
      refine step3 ≫ ?_
      let fn := fun x => (Exists.choose (Y.property.hornFilling h1 h2 x))
      simp [SSet, Closed.rightAdj, MonoidalClosed.closed, Closed.rightAdj, SSet.instCartesianMonoidalCategory,SSet.CartesianClosed,FunctorToTypes.rightAdj]
      fconstructor
      . simp [Functor.functorHom]
        intro xx
        let fn := fun a => Functor.HomObj.ofNatTrans (fn a) (A := (coyoneda.obj (Opposite.op xx)))
        dsimp [Quiver.Hom]
        intro hyp
        apply fn
        let app := hyp.app
        fconstructor
        . let app := hyp.app
          intro c
          apply app
          simp
          sorry
        . sorry
      . sorry
    . sorry

open Simplicial SimplexCategory CategoryTheory SimplexCategory.Truncated Truncated.Hom
  SimplicialObject SimplicialObject.Truncated

def QCatTruncToType (X : SSet.Truncated 2) [SSet.Truncated.Quasicategory₂ X] : Type := X _⦋0⦌₂

#check SSet.Quasicategory₂.comp_unique

#check Quotient

instance QCatTruncToCat (X : SSet.Truncated 2) [SSet.Truncated.Quasicategory₂ X] : Category (X _⦋0⦌₂) where
  Hom x y := by
    refine Quotient { r := SSet.Truncated.HomotopicL (x := x) (y := y), iseqv := ?_ }
    fconstructor
    . intro x
      simp [SSet.Truncated.HomotopicL]
      fconstructor
      exact SSet.Truncated.CompStruct.compId x
    . exact fun {x_2 y_2} a ↦ SSet.Quasicategory₂.HomotopicL.symm a
    . exact fun {x_2 y_2 z} a a_1 ↦ SSet.Quasicategory₂.HomotopicL.trans a a_1
  id x := Quotient.mk _ SSet.Truncated.Edge.id x
  comp {x y z} f g := Quotient.mk _ (Classical.choice (SSet.Truncated.Quasicategory₂.fill21 f g)).fst
  id_comp {x y} f := by
    set cc := Classical.choice _
    rcases cc with ⟨g,h⟩
    simp
    let ci := SSet.Truncated.CompStruct.idComp f
    let hh := SSet.Quasicategory₂.comp_unique h ci
    simp [SSet.Truncated.HomotopicL] at hh





    






      -- fconstructor
      -- . intro x
      --   -- simp [Quiver.Hom]
      --   intro dd
      --   simp [SSet, Closed.rightAdj, MonoidalClosed.closed, Closed.rightAdj, SSet.instCartesianMonoidalCategory,SSet.CartesianClosed]
      --   simp [SSet, Closed.rightAdj, MonoidalClosed.closed, Closed.rightAdj, SSet.instCartesianMonoidalCategory,SSet.CartesianClosed] at dd
      --   let ddd : (Functor.functorHom ((SSet.horn (n + 2) i).toSSet) Y.obj).obj x := by
      --     exact dd


      --   refine Functor.HomObj.ofNatTrans ?_
      --   apply fn
      --   let ddd := (Functor.functorHomEquiv (SSet.horn (n + 2) i).toSSet Y.obj _).invFun dd


      --   apply Functor.natTransEquiv.toFun
      --   let isTerm := CartesianMonoidalCategory.isTerminalTensorUnit (C := SSet)
      --   let Term := Limits.terminal SSet
      --   let step4 : MonoidalCategoryStruct.tensorUnit (SimplexCategoryᵒᵖ ⥤ Type u) ⟶ Limits.terminal SSet :=
      --     Limits.terminal.from (MonoidalCategoryStruct.tensorUnit (SimplexCategoryᵒᵖ ⥤ Type u))

      --   refine step4 ≫ ?_
      --   apply?
      --   dsimp [SSet]
      --   apply?





      --   fconstructor
      --   intro xx
      --   apply dd.app
      --   simp

        -- fconstructor
        -- . intro xx
        --   apply ddd xx
        --   simp



        -- apply Functor.natTransEquiv.toFun
        -- let isTerm := CartesianMonoidalCategory.isTerminalTensorUnit (C := SSet)
        -- fconstructor
        -- . intro xx tr
        --   exact (dd.app xx)








      -- let adj0Fact : (SSet.horn (n + 2) i).toSSet ⟶ Y.obj := by
      --   refine ?_ ≫ adj0
      --   refine (MonoidalCategoryStruct.leftUnitor (SSet.horn (n + 2) i).toSSet).inv ≫ ?_
      --   dsimp
      --   refine MonoidalCategoryStruct.tensorHom ?_ ?_
      --   . sorry
      --   . exact 𝟙 (SSet.horn (n + 2) i).toSSet
      -- let sol1 := Y.property.hornFilling h1 h2 adj0Fact
      -- let f := Exists.choose sol1
      -- refine ?_ ≫ f
      -- apply?










-- def QCat.InternalHom (X Y : SSet.QCat.{u}) : SSet.QCat.{u} := by
--   rcases X with ⟨X,Xh⟩
--   rcases Y with ⟨Y,Yh⟩
--   fconstructor
--   . refine Functor.functorHom X Y
--   . fconstructor
--     intro n i σ0 h1 h2
--     refine ⟨?_,?_⟩

--     . let inst :  Nonempty (SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)) ⟶ Functor.functorHom X Y) := by
--         refine Nonempty.intro ?_
--         refine ?_ ≫ σ0
--         refine SSet.const ?_
--         fconstructor
--         . fconstructor
--           simp
--           exact SimplexCategory.subinterval (↑i + 1) 0 h2
--         . simp
--       apply (Functor.functorHomEquiv _ _ _).invFun
--       fconstructor
--       . intro c ch
--         let σ0' := ((Functor.homObjEquiv _ _ _).toFun ((Functor.functorHomEquiv _ _ _).toFun σ0))
--         unfold SSet at σ0
--         let s0 := curry.obj σ0'
--       -- fconstructor
--       -- . intro c hyp





-- -- instance QCat.SSetEnrichedCat : EnrichedCategory SSet.QCat SSet.QCat where

end
