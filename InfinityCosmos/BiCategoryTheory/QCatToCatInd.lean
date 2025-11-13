import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
import InfinityCosmos.ForMathlib.InfinityCosmos.Goals
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

open Simplicial SimplexCategory CategoryTheory SimplexCategory.Truncated Truncated.Hom
  SimplicialObject SimplicialObject.Truncated

variable (Q : SSet.QCat)

/-(OneTruncation₂ S)-/

abbrev Q2 := ((SSet.truncation 2).obj (Q.obj))

def HomToEdge {x y : (SSet.OneTruncation₂ (Q2 Q))} (f : x ⟶ y) : SSet.Truncated.Edge x y where
  simplex := f.edge
  h₀ := f.src_eq
  h₁ := f.tgt_eq

def EdgeToHom {x y : (SSet.OneTruncation₂ (Q2 Q))} (f : SSet.Truncated.Edge x y) : x ⟶ y := by
  fconstructor
  . exact f.simplex
  . exact f.h₀
  . exact f.h₁

#check Quiver.Path

noncomputable def PathRw (x y : (SSet.OneTruncation₂ (Q2 Q))) (P : Quiver.Path x y) : x ⟶ y := by
  induction P
  . exact 𝟙rq x
  . rename_i z w p g f
    let inst : SSet.Truncated.Quasicategory₂ (Q2 Q) := by
      apply @SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc _ ?_
      apply Q.property
    exact EdgeToHom _ (Classical.choice (inst.fill21 (HomToEdge _ f) (HomToEdge _ g))).fst

theorem NonEptyElim' (α : Type*) (ne : Nonempty α) (P : α → Prop) (h : ∀(x : α), (P x)) : P (Classical.choice ne) := by
  exact h (Classical.choice ne)

noncomputable def PathRwComp (x y z : (SSet.OneTruncation₂ (Q2 Q))) (f : Quiver.Path x  y) (g : y ⟶ z) : SSet.Truncated.CompStruct (HomToEdge Q (PathRw Q _ _ f)) (HomToEdge Q g) (HomToEdge Q (PathRw Q x z (f.cons g))) := by
  simp [PathRw]
  set ccrw := (Classical.choice _)
  let cc' := ccrw.snd
  rcases cc' with ⟨s,h1,h2,h3⟩
  simp [HomToEdge,Quiver.Hom.toPath,EdgeToHom] at h1 h2 h3
  fconstructor
  . exact s
  . simp [HomToEdge,h1]
    exact rfl
  . simp [h2,HomToEdge]
  . simp [h3,HomToEdge,EdgeToHom]

def HomToPath (x y : (SSet.OneTruncation₂ (Q2 Q))) (f : x ⟶ y) : Quiver.Path x y := by
  exact f.toPath

#check SSet.Truncated.HoRel₂


noncomputable def FRRRw (x y : (SSet.OneTruncation₂ (Q2 Q))) (P : Quiver.Path x y): x ⟶ y := by
  induction P
  . exact 𝟙rq x
  . rename_i z w p f g
    let inst : SSet.Truncated.Quasicategory₂ (Q2 Q) := by
      apply @SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc _ ?_
      apply Q.property
    exact EdgeToHom _ (Classical.choice (inst.fill21 (HomToEdge _ g) (HomToEdge _ f))).fst

theorem PathRwSimplex (x y : (SSet.OneTruncation₂ (Q2 Q))) (P : Quiver.Path x y) : (Quotient.functor SSet.Truncated.HoRel₂).map ((Cat.FreeRefl.quotientFunctor _ ).map (PathRw Q x y P).toPath) = (Quotient.functor SSet.Truncated.HoRel₂).map ((Cat.FreeRefl.quotientFunctor _ ).map P) := by
  induction P
  . congr 1
    simp [PathRw,Cat.FreeRefl.quotientFunctor,Cat.FreeReflRel]
    refine (Functor.homRel_iff (Quotient.functor Cat.FreeReflRel) (𝟙rq x).toPath Quiver.Path.nil).mp ?_
    refine(Quotient.functor_homRel_eq_compClosure_eqvGen Cat.FreeReflRel (𝟙rq x).toPath Quiver.Path.nil).mpr ?_
    fconstructor
    simp [Quiver.Hom.toPath]
    refine Quotient.CompClosure.of Cat.FreeReflRel (Quiver.Path.nil.cons (𝟙rq x)) Quiver.Path.nil ?_
    apply Cat.FreeReflRel.mk
  . rename_i z w p f h
    simp [PathRw]
    simp [PathRw] at h
    let rwh1 : (p.cons f) =  Quiver.Path.comp p f.toPath := by
      exact rfl
    let rwh2 : Quiver.Path.comp p f.toPath = (Paths.categoryPaths _).comp p f.toPath  := by
      exact rwh1
    rw [rwh1,rwh2]
    rw [(Cat.FreeRefl.quotientFunctor (SSet.OneTruncation₂ (Q2 Q))).map_comp,(Quotient.functor SSet.Truncated.HoRel₂).map_comp, <- h]
    refine CategoryTheory.Quotient.sound SSet.Truncated.HoRel₂ ?_
    let twocl := PathRwComp Q x z w p f
    fapply SSet.Truncated.HoRel₂.mk'
    . exact twocl.simplex
    . simp [twocl.h₀₁,PathRw,HomToEdge]
    . simp [twocl.h₁₂,PathRw,HomToEdge]
    . simp [twocl.h₀₂,PathRw,HomToEdge]

universe u

-- structure QuasiFunctor' (Q :  SSet.Truncated 2) [SSet.Truncated.Quasicategory₂ Q] (C : Type u) [Category C] where
--   obj : (Q _⦋0⦌₂)→ C
--   map {x y : Q _⦋0⦌₂} : SSet.Truncated.Edge x y → (obj x ⟶ obj y)
--   map_comp {x y z : Q _⦋0⦌₂} (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z) (h : SSet.Truncated.Edge x z) (cs : SSet.Truncated.CompStruct f g h) : (map f) ≫ (map g) = (map h)
--   map_hom {x y : Q _⦋0⦌₂} (f g : SSet.Truncated.Edge x y) (HL : SSet.Truncated.HomotopicL f g) : map f = map g
--   map_id (x : Q _⦋0⦌₂) : map (SSet.Truncated.Edge.id x) = 𝟙 obj x

-- def QuasiFunctor (Q : SSet.QCat) (C : Type u) [Category C] := @QuasiFunctor' ((SSet.truncation 2).obj Q.obj) (@SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc Q.obj Q.property) C _


-- /-Paths (SSet.OneTruncation₂ ((SSet.truncation 2).obj Q.obj)) ⥤ C-/
-- noncomputable def QuasiFunctorToFunctor'' {Q : SSet.QCat} {C : Type u} [Category C] (QF : QuasiFunctor Q C) : Paths (SSet.OneTruncation₂ ((SSet.truncation 2).obj Q.obj)) ⥤ C where
--   obj x := by
--     let inst : ((SSet.truncation 2).obj Q.obj).Quasicategory₂ := (@SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc Q.obj Q.property)
--     exact QF.obj x
--   map f := by
--     let inst : ((SSet.truncation 2).obj Q.obj).Quasicategory₂ := (@SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc Q.obj Q.property)
--     apply QF.map
--     exact HomToEdge Q (PathRw _ _ _ f)
--   map_id x := by
--     let inst : ((SSet.truncation 2).obj Q.obj).Quasicategory₂ := (@SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc Q.obj Q.property)
--     exact (QF.map_id x)
--   map_comp {X Y Z}f g := by
--     let inst : ((SSet.truncation 2).obj Q.obj).Quasicategory₂ := (@SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc Q.obj Q.property)
--     dsimp
--     rw [<- QF.map_comp]
--     let cs := PathRwComp Q X Y Z f (PathRw Q Y Z g)
--     simp [CategoryStruct.comp]
--     refine Classical.choice (SSet.Quasicategory₂.transport_edge₁ cs ?_)
--     induction g
--     . simp
--       have lem : (PathRw Q Y Y Quiver.Path.nil) = ?_ := by
--         simp [PathRw]
--       . apply 𝟙rq
--       rw [lem]
--       apply?



section main
variable (X Y Z : SSet.QCat)

noncomputable def QCatHomToNatTrans (f : QCat.Bicategory.Hom X Y) : X.obj ⟶ Y.obj := by
  rcases f with ⟨⟨f⟩⟩
  unfold  SimplicialCategory.QCat.SSetEnrichedCat SimplicialCategory.QCat.SimplicialCat at f
  apply CategoryTheory.Functor.natTransEquiv.toFun
  refine ?_ ≫ (yonedaEquiv.invFun f)
  refine Limits.IsTerminal.from ?_ (MonoidalCategoryStruct.tensorUnit (SimplexCategoryᵒᵖ ⥤ Type))
  apply Limits.evaluationJointlyReflectsLimits
  intro k
  simp [inclusion,yoneda,Functor.mapCone,evaluation,Limits.Cones.functoriality]
  refine Limits.IsLimit.ofExistsUnique ?_
  intro s
  fconstructor
  . simp [Quiver.Hom,SimplexCategory.Hom]
    intro s
    fconstructor
    . exact fun _ => {val := 0, isLt := by simp}
    . exact monotone_const
  . simp
    intro y
    ext n x
    simp


noncomputable def NatTransToQCatHom (f : X.obj ⟶ Y.obj) : QCat.Bicategory.Hom X Y := by
  fconstructor
  fconstructor
  simp [SSet.OneTruncation₂,SSet.truncation,truncation]
  unfold  SimplicialCategory.QCat.SSetEnrichedCat SimplicialCategory.QCat.SimplicialCat
  apply yonedaEquiv.toFun
  refine CategoryStruct.comp ?_  ?_ (Y := MonoidalCategoryStruct.tensorUnit (SSet))
  . exact CartesianMonoidalCategory.toUnit (yoneda ^⦋0⦌)
  . apply CategoryTheory.Functor.natTransEquiv.invFun
    exact f


#check Equiv
noncomputable def QCatHomNatTransEquiv : (QCat.Bicategory.Hom X Y) ≃ (X.obj ⟶ Y.obj) where
  toFun := QCatHomToNatTrans X Y
  invFun := NatTransToQCatHom X Y
  left_inv := by
    simp [Function.LeftInverse]
    intro f
    simp [QCatHomToNatTrans,NatTransToQCatHom,yonedaEquiv, Functor.natTransEquiv]
    rcases f with ⟨⟨f⟩⟩
    simp [CategoryTheory.Quotient]
    congr
    simp [Paths] at f
    simp [Functor.HomObj.ofNatTrans]
    rcases f with ⟨ap,na⟩
    simp
    congr
    ext x y z
    simp [Functor.functorHom]
    congr
    simp [inclusion] at y
    rcases y with ⟨y⟩
    simp at y
    refine SimplexCategory.Hom.ext_iff.mpr ?_
    ext w
    simp
  right_inv := by
    simp [Function.RightInverse,Function.LeftInverse]
    intro f
    simp [QCatHomToNatTrans,NatTransToQCatHom,yonedaEquiv, Functor.natTransEquiv]
    ext n a
    simp [Functor.HomObj.ofNatTrans,Functor.functorHom]

#check SSet.Truncated.HoRel₂

#check Paths


-- theorem CompStruct (f : QCat.Bicategory.Hom X Y) (g : QCat.Bicategory.Hom Y Z) : ((QCatHomNatTransEquiv _ _).toFun f) ≫ ((QCatHomNatTransEquiv _ _).toFun g) = (QCatHomNatTransEquiv _ _).toFun (f ≫ g) := by




  -- have lem : f ≫ g = CategoryTheory.Quotient.mk (CategoryTheory.Quotient.mk (Quiver.Path.comp sorry) (r := Cat.FreeReflRel)) (r :=  SSet.Truncated.HoRel₂) := by
  --   simp [CategoryStruct.comp,eComp, EnrichedCategory.comp,EnrichedCategory.comp]
  --   have h : (SSet.hoFunctor.map (EnrichedCategory.comp X Y Z)).obj ((Functor.LaxMonoidal.μ SSet.hoFunctor (EnrichedCategory.Hom X Y) (EnrichedCategory.Hom Y Z)).obj (f, g)) = ((Functor.LaxMonoidal.μ SSet.hoFunctor (EnrichedCategory.Hom X Y) (EnrichedCategory.Hom Y Z)) ≫ (SSet.hoFunctor.map (EnrichedCategory.comp X Y Z))).obj (f,g) := by
  --     simp
  --   rw [h]
  --   let h' := Functor.LaxMonoidal.μ_natural (F := SSet.hoFunctor) (X := (EnrichedCategory.Hom X Y)) (X' := (EnrichedCategory.Hom Y Z))








end main





def QuasiFunctorToFunctor' {Q : SSet.QCat} {C : Type u} [Category C] (QF : QuasiFunctor Q C) : Cat.FreeRefl (SSet.OneTruncation₂ ((SSet.truncation 2).obj Q.obj)) ⥤ C := by
  fapply CategoryTheory.Quotient.lift

def QuasiFunctorToFunctor {Q : SSet.QCat} {C : Type u} [Category C] (QF : QuasiFunctor Q C) : (SSet.hoFunctor.obj Q.obj) ⥤ C := by
  let inst : ((SSet.truncation 2).obj Q.obj).Quasicategory₂ := (@SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc Q.obj Q.property)
  fapply CategoryTheory.Quotient.lift
  -- . fconstructor
  --   fconstructor
  --   . intro x
  --     apply QF.obj
  --     rcases x with ⟨x⟩
  --     exact x
  --   . intro X Y f
  --     apply QF.map
  --     rcases X with ⟨X⟩
  --     rcases Y with ⟨Y⟩
  --     simp [Quiver.Hom, Cat.FreeRefl, Quotient.Hom, Cat.FreeReflRel] at f
  --     refine Quot.lift ?_ ?_ f
  --     . intro P
  --       let P' := PathRw _ _ _ P
  --       simp
  --       exact HomToEdge _ P'
  --     . intro a b h
  --       simp [HomToEdge]





  -- . intro x y f g h







  -- obj x := by
  --   let inst : ((SSet.truncation 2).obj Q.obj).Quasicategory₂ := (@SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc Q.obj Q.property)
  --   refine QF.obj ?_
  --   simp [SSet.hoFunctor, SSet.Truncated.hoFunctor₂] at x
  --   rcases x with ⟨⟨a⟩⟩
  --   simp [Paths] at a
  --   exact a
  -- map {X Y} f := by
  --   let inst : ((SSet.truncation 2).obj Q.obj).Quasicategory₂ := (@SSet.Truncated.two_truncatation_of_qc_is_2_trunc_qc Q.obj Q.property)
  --   refine QF.map ?_
  --   rcases X with ⟨⟨X⟩⟩
  --   rcases Y with ⟨⟨Y⟩⟩
  --   simp
