import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Bicategory.Functor.Lax
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

universe v u

open CategoryTheory

def Bicategory.LaxFunctor.Const (C : Type u) {D : Type v} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] (x : D) : OplaxFunctor C D where
    obj _ := x
    map _ := 𝟙 x
    map₂ _ := 𝟙 (𝟙 x)
    mapId _ := 𝟙 (𝟙 x)
    mapComp _ _ := eqToHom (Category.comp_id (𝟙 x)).symm
    map₂_associator := by simp[Bicategory.Strict.associator_eqToIso]
    map₂_leftUnitor := by simp[Bicategory.Strict.leftUnitor_eqToIso]
    map₂_rightUnitor := by simp[Bicategory.Strict.rightUnitor_eqToIso]

structure Bicategory.Cone {C : Type u} {D : Type v} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] (F : OplaxFunctor C D) where
   pt : D
   π : Oplax.OplaxTrans (Bicategory.LaxFunctor.Const C pt) F

def Bicategory.ConstNT (C : Type u) {D : Type v} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] {x y : D} (f : x ⟶ y) : Oplax.OplaxTrans (Bicategory.LaxFunctor.Const C x) (Bicategory.LaxFunctor.Const C y) where
    app _ := f
    naturality {a b} g := by
      refine eqToHom ?_
      simp [LaxFunctor.Const]
    naturality_naturality η := by
      simp [LaxFunctor.Const]
    naturality_id _ := by
      simp [LaxFunctor.Const,Bicategory.Strict.leftUnitor_eqToIso,Bicategory.Strict.rightUnitor_eqToIso]
    naturality_comp g h := by
      simp [LaxFunctor.Const,Bicategory.Strict.associator_eqToIso]

structure Bicategory.Cone.Hom {C : Type u} {D : Type v} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] {F : OplaxFunctor C D} (A B : Bicategory.Cone F) where
    map : A.pt ⟶ B.pt
    nat : A.π = Oplax.OplaxTrans.vcomp (Bicategory.ConstNT C map) B.π

structure Bicategory.Lim {C : Type u} {D : Type v} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] (F : OplaxFunctor C D) where
    cone : Bicategory.Cone F
    exis (c : Bicategory.Cone F): Bicategory.Cone.Hom c cone
    uniq (c : Bicategory.Cone F) (f : Bicategory.Cone.Hom c cone) : f.map ≅ (exis c).map
    uniq_uniq (c : Bicategory.Cone F) (f : Bicategory.Cone.Hom c cone) (iso : f.map ≅ (exis c).map) : uniq c f = iso

abbrev BiWalkingCospan := CategoryTheory.LocallyDiscrete Limits.WalkingCospan

structure Bicategory.pullback {C : Type v} [Bicategory C] [Bicategory.Strict C] (F : OplaxFunctor (BiWalkingCospan) C) where
  cone : Bicategory.Cone F
  ump : Bicategory.Lim F

def Bicategory.pullback.conemk {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} (f : a ⟶ b) (g : c ⟶ b) : OplaxFunctor (BiWalkingCospan) C :=
  CategoryTheory.Pseudofunctor.toOplax (Functor.toPseudoFunctor (CategoryTheory.Limits.cospan f g))

abbrev Bicategory.pullback.of {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} (f : a ⟶ b) (g : c ⟶ b) :=
  Bicategory.pullback (Bicategory.pullback.conemk f g)

def Bicategory.pullback.pt {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} {f : a ⟶ b} {g : c ⟶ b} (pb : Bicategory.pullback.of f g) : C :=
  pb.cone.pt

def Bicategory.pullback.fst {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} {f : a ⟶ b} {g : c ⟶ b} (pb : Bicategory.pullback.of f g) : Bicategory.pullback.pt pb ⟶ a :=
  pb.cone.π.app {as := Limits.WalkingCospan.left}

def Bicategory.pullback.snd {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} {f : a ⟶ b} {g : c ⟶ b} (pb : Bicategory.pullback.of f g) : Bicategory.pullback.pt pb ⟶ c :=
  pb.cone.π.app {as := Limits.WalkingCospan.right}
