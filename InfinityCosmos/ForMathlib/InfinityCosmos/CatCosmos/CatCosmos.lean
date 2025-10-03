import InfinityCosmos.ForMathlib.InfinityCosmos.CatCosmos.FunctorIsoFib
import InfinityCosmos.ForMathlib.InfinityCosmos.CatCosmos.BicategoryToCosmos
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

noncomputable section
open CategoryTheory

universe u

instance : PreInfinityCosmos (SSetEnriched Cat.{u,u}) where
  has_qcat_homs {_ _} := Nerve.quasicategory
  IsIsofibration {_ _} f := Functor.IsIsofibration1 f

theorem ecy (X : SSetEnriched Cat.{u,u}): (eCoyoneda SSet X) = (@eCoyoneda _ _ _ _ _ (biCatAsCatEnrichedOrdinary Cat.{u,u}) X) ⋙ nerveFunctor := by
  exact rfl

#check Functor.precomp_map_heq


def HomFunc (X : SSetEnriched Cat.{u,u}) : Cat.{u,u} ⥤ Cat.{u,u} where
  obj a := Cat.of (X ⟶ a)
  map {a b} f := by
    exact @Bicategory.postcomp Cat.{u,u} _ _ _ X f

def ProdFunc (X : SSetEnriched Cat.{u,u}) : Cat.{u,u} ⥤ Cat.{u,u} where
  obj A := Cat.of (A × X.α)
  map {A B} f := by
    refine Functor.toCatHom (Functor.prod f (𝟙 X))


def adjunc (X : SSetEnriched Cat.{u,u}) : (ProdFunc X) ⊣ (@eCoyoneda _ _ _ _ _ (biCatAsCatEnrichedOrdinary Cat.{u,u}) X) := by
  refine Adjunction.mkOfHomEquiv ?_
  refine { homEquiv := ?_, homEquiv_naturality_left_symm := ?_, homEquiv_naturality_right := ?_ }
  . intro Y Z
    let cc := (@currying Y _ X.α _ Z _).symm
    refine Equiv.ofBijective ?_ ?_
    . exact cc.functor.obj
    . fconstructor
      . intro a b h
        simp [cc,currying] at h
        exact Functor.curry_obj_injective h
      . intro b
        simp [cc,currying]
        use uncurry.obj b
        simp [Functor.curry_obj_uncurry_obj]
  . intro A B C f g
    simp [Equiv.ofBijective,ProdFunc]
    apply Functor.hext
    . intro a
      rcases a with ⟨a1,a2⟩
      simp [Functor.prod,Functor.toCatHom,Function.surjInv]
      apply?

















-- theorem ecy' (X : SSetEnriched Cat.{u,u}): @eCoyoneda _ _ _ _ _ (biCatAsCatEnrichedOrdinary Cat.{u,u}) X = HomFunc X := by
--   fapply Functor.hext
--   . intro a
--     exact rfl
--   . intro a b f
--     simp
--     apply Functor.hext
--     . intro q
--       exact rfl
--     . intro q r g
--       simp [HomFunc,Bicategory.whiskerRight,whiskerRight]
--       apply NatTrans.ext
--       funext s
--       simp[eHomWhiskerLeft,EnrichedCategory.Hom,MonoidalCategoryStruct.whiskerLeft,Cat.isLimitProdCone,Limits.BinaryFan.isLimitMk,Cat.prodCone]
--       simp [MonoidalCategoryStruct.rightUnitor]
--       simp [Cat.isLimitProdCone,Limits.BinaryFan.isLimitMk,Limits.BinaryFan.mk,Limits.IsLimit.lift]
--       simp [Limits.BinaryFan.fst]

--       simp [eHomWhiskerLeft, MonoidalCategoryStruct.rightUnitor ,Bicategory.Strict.rightUnitor_eqToIso]
--       apply?

-- def ecy' (X : SSetEnriched Cat.{u,u}): @eCoyoneda _ _ _ _ _ (biCatAsCatEnrichedOrdinary Cat.{u,u}) X ≅ HomFunc X where
--   hom := by
--     fconstructor
--     . intro c
--       exact 𝟙 (Cat.of (X ⟶ c))
--     . intro c d f
--       simp [CategoryStruct.comp, CategoryStruct.id,Functor.id,Functor.comp]
--       apply Functor.hext
--       . intro q
--         exact rfl
--       . intro q p r
--         simp














theorem pl (X : SSetEnriched Cat.{u,u}): Limits.PreservesLimits (eCoyoneda SSet X) := by
  rw [ecy]
  refine { preservesLimitsOfShape := ?_ }
  intro J _
  refine { preservesLimit := ?_ }
  intro F
  refine @Limits.comp_preservesLimit _ _ _ _ _ _ _ _ _ _ _ ?_ ?_
  . refine { preserves := ?_ }
    intro c hc
    refine Nonempty.intro ?_
    fconstructor
    . intro s
      simp [EnrichedCategory.Hom,Quiver.Hom]
      refine curryObj ?_
      let scone : Limits.Cone F := by
        fconstructor
        . exact Cat.of (s.pt × (@Bundled.α Category.{u, u} X))
        . simp [Functor.const]
          fconstructor
          . intro x
            simp
            rcases s with ⟨spt,⟨sapp,snat⟩⟩
            simp
            let tttt := sapp x
            simp [EnrichedCategory.Hom,Cat.of,Quiver.Hom,Bundled.of] at tttt
            let ttt := uncurry.obj tttt
            exact ttt
          . intro x y f
            rcases s with ⟨spt,⟨sapp,snat⟩⟩
            let snat' := snat f
            simp
            simp at snat'
            rw [snat']
            fapply Functor.hext
            . intro pair
              exact rfl
            . intro pair1 pair2 g
              refine Functor.hcongr_hom ?_ g
              refine Functor.curry_obj_injective ?_
              simp[curry]
              fapply Functor.hext
              . intro a
                fapply Functor.hext
                . intro b
                  exact rfl
                . intro b1 b2 bf
                  sorry
              . sorry













              sorry
      simp at scone
      exact (hc.lift scone)
    . intro s j
      simp [curryObj]
      sorry








instance : InfinityCosmos (SSetEnriched Cat.{u,u}) where
  has_products := by
    refine { hasConicalLimitsOfShape := fun(J) => ?_ }
    refine { hasConicalLimit := fun(F) => ?_  }
    refine { toHasLimit := ?_, preservesLimit_eCoyoneda := ?_ }
    . refine { exists_limit := ?_ }
      refine Nonempty.intro ?_
      exact { cone := Cat.HasLimits.limitCone F, isLimit := Cat.HasLimits.limitConeIsLimit F}
    . intro X
      simp [eCoyoneda,eHomFunctor,EnrichedCategory.Hom]
      refine { preserves := ?_ }
      intro c hc
      refine Nonempty.intro ?_
      fconstructor
      . intro s
        rcases s with ⟨pt,⟨app,nat⟩⟩
        simp at app
        simp
        apply (Adjunction.homEquiv nerveAdjunction pt (Cat.of (X ⟶ c.pt))).toFun
        rcases c with ⟨cpt,⟨capp,cnat⟩⟩
        simp
        let cm : (@Bundled.α Category.{u, u} X) → Limits.Cone F := by
          intro x
          fconstructor
          . exact Cat.of (X ⟶ cpt)
          . fconstructor
            . intro X1
              simp
              fconstructor
              fconstructor
              . intro xc
                simp at xc
                refine (capp X1).obj ?_
                simp
                apply xc.obj x
              . intro a b f
                simp
                refine (capp X1).map ?_
                apply f.app
              . intro a
                simp [Cat.of,Bundled.of] at a
                simp [CategoryStruct.id]
                sorry
              . sorry
            . sorry







    -- . intro X
    --   refine { preserves := ?_ }
    --   intro c hc
    --   refine Nonempty.intro ?_
    --   refine Limits.IsLimit.ofExistsUnique ?_
    --   intro s
    --   simp [eCoyoneda,eHomFunctor,EnrichedCategory.Hom,eHomWhiskerLeft,Functor.mapCone,Limits.Cones.functoriality]
    --   refine existsUnique_of_exists_of_unique ?_ ?_
    --   . fconstructor
    --     . rcases s with ⟨pt,h⟩
    --       simp
    --       rcases h with ⟨app,nat⟩
    --       simp [EnrichedCategory.Hom] at app
    --       let app' : (X_1 : Discrete J) → ((SSet.hoFunctor.obj pt) ⟶ (Cat.of (X ⟶ (F.obj X_1)))) := by
    --         intro X_1
    --         apply (Adjunction.homEquiv nerveAdjunction pt (Cat.of (X ⟶ F.obj X_1))).invFun
    --         exact app X_1
    --       let ggg := hc.lift

    --       apply (Adjunction.homEquiv nerveAdjunction pt (Cat.of (X ⟶ c.pt))).toFun

          -- let s : Limits.Cone F := by
          --   fconstructor
          --   . exact (SSet.hoFunctor.obj pt)
          --   . fconstructor
          --     . simp
          --       intro x
          --       apply (Adjunction.homEquiv nerveAdjunction pt _).invFun
          --       refine (app x) ≫ ?_
          --       have rwrw : nerve (X ⟶ F.obj x) = nerveFunctor.obj (Cat.of (X ⟶ F.obj x)) := rfl
          --       rw [rwrw]
          --       apply nerveFunctor.map
          --       simp [Quiver.Hom]
          --       have ye := yonedaEquiv



          --       apply?



          -- simp at nat
          -- have tt : s.pt = (nerve _) := by
          --   rcases s
