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

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ w₁

def Functor.IsIsofibration1 {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D): Prop
  := ∀(c : C) (d : D) (φ : F.obj c ≅ d), ∃ (c' : C) (ψ : c ≅ c') (h : F.obj c' = d), F.map ψ.hom = φ.hom ≫ eqToHom h.symm

def Bicategory.IsIsofibration (C : Type u₁) [Bicategory.{v₁,w₁,u₁} C] [Bicategory.Strict C] : MorphismProperty C := by
    intro X Y f
    refine ∀(Z : C), ?_
    let tt := ((Bicategory.postcomposing Z X Y).obj f)
    apply Functor.IsIsofibration1 tt

def IsoCat : Type u₃ := ULift.{u₃} Bool

def IsoCat.mk (b : Bool) : IsoCat := ULift.up b

instance : Category.{v₃,u₃} IsoCat where
  Hom a b := PUnit
  id a := PUnit.unit
  comp := by
    intros
    exact PUnit.unit

def IsoCat.fst : PUnit ⥤ IsoCat where
  obj _ := ULift.up false
  map f := PUnit.unit

def IsoCatIso : (IsoCat.mk false) ≅ (IsoCat.mk true) where
  hom := PUnit.unit
  inv := PUnit.unit

def IsoToIsoCat {C : Type u₁} [Category.{v₁} C] {a b : C} (i : a ≅ b) : IsoCat ⥤ C where
  obj X := by
    cases X.down
    . exact a
    . exact b
  map {X Y} f := by
    cases X.down
    . cases Y.down
      . exact 𝟙 a
      . exact i.hom
    . cases Y.down
      . exact i.inv
      . exact 𝟙 b
  map_id X := by
    cases X.down
    . simp
    . simp
  map_comp {X Y Z} f g := by
    cases X.down
    . cases Y.down
      . cases Z.down
        . simp
        . simp
      . cases Z.down
        . simp
        . simp
    . cases Y.down
      . cases Z.down
        . simp
        . simp
      . cases Z.down
        . simp
        . simp

def IsoCatToIso {C : Type u₁} [Category.{v₁} C] (F : IsoCat ⥤ C) : (F.obj (IsoCat.mk false)) ≅ (F.obj (IsoCat.mk true)) := by
  refine F.mapIso ?_
  exact IsoCatIso

def Functor.IsIsofibration2 {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) : Prop :=
  ∀ (bott : Functor.{u₃, v₂, u₃, u₂} IsoCat D) (top : Functor.{0, v₁, 0, u₁} PUnit C), (IsoCat.fst ⋙ bott = top ⋙ F) →
    ∃ (lift : Functor.{u₃, v₁, u₃, u₁} IsoCat C), ((lift ⋙ F = bott) ∧ (IsoCat.fst ⋙ lift = top))


theorem Helper' {C : Type u₁} [Category.{v₁} C] {a1 b1 a2 b2 : C}
  (eq1 : a1 = a2) (eq2 : b1 = b2): (a1 ≅ b1) = (a2 ≅ b2) := by
    simp [eq1,eq2]

theorem Helper {C : Type u₁} [Category.{v₁} C] {a1 b1 a2 b2 : C} {p1 : a1 ≅ b1} {p2 : a2 ≅ b2}
  (eq1 : a1 = a2) (eq2 : b1 = b2): (cast (Helper' eq1 eq2) p1).hom ≍ p1.hom := by
    cases eq1
    cases eq2
    simp

theorem Helper'' {C : Type u₁} [Category.{v₁} C] {a1 b1 a2 b2 : C} {p1 : a1 ≅ b1} {p2 : a2 ≅ b2}
  (eq1 : a1 = a2) (eq2 : b1 = b2): p1.inv ≍ (cast (Helper' eq1 eq2) p1).inv := by
    cases eq1
    cases eq2
    simp

theorem Helper2 {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] {a b : C} {p : a ≅ b}
  (F : C ⥤ D) : (F.map p.inv) = (F.mapIso p).inv := by
    exact rfl

theorem Bimpy {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) : (Functor.IsIsofibration1 F) → (Functor.IsIsofibration2 F) := by
  simp [Functor.IsIsofibration1,Functor.IsIsofibration2]
  intro h bott top comm
  have h'''' : (IsoCat.fst.obj PUnit.unit) = (IsoCat.mk false) := by
    simp [IsoCat.fst,IsoCat.mk]
  let iso' : F.obj (top.obj PUnit.unit) ≅ bott.obj (IsoCat.mk true) := by
    let toto := Functor.congr_obj comm PUnit.unit
    simp at toto
    rw [<- toto, h'''']
    exact IsoCatToIso bott
  let h' := h (top.obj PUnit.unit) (bott.obj (IsoCat.mk true)) iso'
  rcases h' with ⟨c,⟨ψ,⟨h,eq1⟩⟩⟩
  use IsoToIsoCat ψ
  let abc := (Functor.congr_obj comm PUnit.unit)
  simp at abc
  refine ⟨?_,?_⟩
  . fapply Functor.hext
    . intro x
      induction x
      rename_i x
      cases x
      . simp [IsoToIsoCat, <- abc, IsoCat.fst]
      . simp [IsoToIsoCat,h,IsoCat.mk]
    . intro x y f
      simp [IsoToIsoCat]
      induction x
      rename_i x
      cases x
      . induction y
        rename_i y
        cases y
        . simp [<- abc]
          rw [<- abc]
          refine Quiver.heq_of_homOfEq_ext rfl rfl ?_
          simp
          let cde : f = 𝟙 _ := by
            cases f
            simp [CategoryStruct.id]
          rw [cde]
          exact Eq.symm (bott.map_id { down := false })
        . simp [eq1,iso',<- abc]
          set eqeq := Eq.symm (id (congrArg (fun _a ↦ _a ≅ bott.obj (IsoCat.mk true)) (Eq.symm (Functor.congr_obj comm PUnit.unit))))
          have leg1 : (cast eqeq (IsoCatToIso bott)).hom ≍ (IsoCatToIso bott).hom := by
            apply Helper
            . simp [<- abc,IsoCat.mk,IsoCat.fst]
              refine bott.mapIso ?_
              exact IsoCatIso
            . simp [<- abc,IsoCat.mk,IsoCat.fst]
            . simp
          exact leg1
      . induction y
        rename_i y
        cases y
        . simp
          let wer : f = IsoCatIso.inv := by
            cases f
            simp [IsoCatIso]
          rw [wer]
          rw [Helper2,Helper2]
          apply HEq.symm
          refine Quiver.heq_of_homOfEq_ext (id (Eq.symm h)) abc ?_
          refine (Iso.inv_ext ?_).symm
          simp [eq1]
          refine (IsIso.eq_inv_comp iso'.hom).mp ?_
          simp
          apply HEq.eq
          refine
            (eqToHom_comp_heq_iff (Quiver.homOfEq (bott.map IsoCatIso.inv) (id (Eq.symm h)) abc)
                  iso'.inv (Functor.IsIsofibration1._proof_1 F (bott.obj (IsoCat.mk true)) c h)).mpr
              ?_
          refine HEq.trans ?_ ?_ (b := bott.map IsoCatIso.inv)
          . exact Quiver.homOfEq_heq (id (Eq.symm h)) abc (bott.map IsoCatIso.inv)
          . simp [iso',IsoCatToIso]
            let rrr : bott.map IsoCatIso.inv = (bott.mapIso IsoCatIso).inv := by
              simp
            rw [rrr]
            set eqeq := Eq.symm (id (congrArg (fun _a ↦ _a ≅ bott.obj (IsoCat.mk true)) (Eq.symm (Functor.congr_obj comm PUnit.unit))))
            have ng : (bott.mapIso IsoCatIso) ≍ (cast eqeq (bott.mapIso IsoCatIso)) := by
              simp
            apply Helper''
            . simp [<- abc,IsoCat.mk,IsoCat.fst]
              refine bott.mapIso ?_
              exact IsoCatIso
            . simp [<- abc,IsoCat.mk,IsoCat.fst]
            . simp
        . simp
          rw [h]
          let cde : f = 𝟙 _ := by
            cases f
            simp [CategoryStruct.id]
          rw [cde]
          simp [IsoCat.mk]
  . fapply Functor.hext
    . intro x
      simp [IsoCat.fst,IsoToIsoCat]
    . intro x y f
      simp [IsoCat.fst,IsoToIsoCat]
      let cde : f = 𝟙 _ := by
        cases f
        simp [CategoryStruct.id]
      rw[cde]
      simp

def constff {C : Type u₁} [Category.{v₁} C] (c : C) : PUnit.{1} ⥤ C where
  obj _ := c
  map _ := 𝟙 c

theorem Bimpy2 {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) : (Functor.IsIsofibration2 F) → (Functor.IsIsofibration1 F) := by
  simp [Functor.IsIsofibration1,Functor.IsIsofibration2]
  intro h c d φ
  let io : IsoCat.fst ⋙ IsoToIsoCat φ = constff c ⋙ F := by
    fapply Functor.hext
    . intro x
      simp [IsoToIsoCat,IsoCat.fst,constff]
    . intro x y f
      simp [IsoToIsoCat,IsoCat.fst,constff]
  let h' := h (IsoToIsoCat φ) (constff c) io
  rcases h' with ⟨lift,⟨eq1,eq2⟩⟩
  use lift.obj {down := true}
  let eq3 : c ≅ lift.obj { down := true } := by
    have temp := Functor.congr_obj eq2 PUnit.unit
    simp [constff,IsoCat.fst ] at temp
    let ii := (eqToIso temp).symm
    refine Iso.trans ii ?_
    refine lift.mapIso ?_
    exact IsoCatIso
  use eq3
  have eq4 :  F.obj (lift.obj { down := true }) = d := by
    have temp := Functor.congr_obj eq1 { down := true }
    simp [IsoToIsoCat] at temp
    exact temp
  use eq4
  simp [eq3,eqToHom_map]
  refine
    (eqToHom_comp_iff (congr_arg F.obj (Eq.symm (Functor.congr_obj eq2 PUnit.unit)))
          (φ.hom ≫ eqToHom (Functor.IsIsofibration1._proof_1 F d (lift.obj { down := true }) eq4))
          (F.map (lift.map IsoCatIso.hom))).mpr
      (Functor.congr_hom eq1 IsoCatIso.hom)
