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

def Bicategory.pullback.Diagrammk {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} (f : a ⟶ b) (g : c ⟶ b) : OplaxFunctor (BiWalkingCospan) C :=
  CategoryTheory.Pseudofunctor.toOplax (Functor.toPseudoFunctor (CategoryTheory.Limits.cospan f g))
/--/ { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd
         naturality := by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) j <;> cases j <;> simp [eq] } -/

theorem Disc {a b : BiWalkingCospan} {f : a ⟶ b} (η : f ⟶ f) : η = 𝟙 f := by
  exact rfl

theorem Disc2 {a b : BiWalkingCospan} (f g : a ⟶ b) : f = g := by
  rcases a with ⟨a⟩ 
  rcases b with ⟨b⟩
  rcases f with ⟨f⟩ 
  rcases g with ⟨g⟩
  cases a <;> cases b <;> cases f <;> cases g
  . simp
  . simp 
  . simp

theorem Disc3 {a b : BiWalkingCospan} {f g : a ⟶ b} (η : f ⟶ g) : η = eqToHom (Disc2 f g)  := by
  rcases a with ⟨a⟩ 
  rcases b with ⟨b⟩
  rcases f with ⟨f⟩ 
  rcases g with ⟨g⟩
  rcases η with ⟨⟨η⟩⟩
  cases a <;> cases b <;> cases f <;> cases g 
  . exact rfl
  . exact rfl
  . exact rfl

#check Bicategory.Strict.leftUnitor_eqToIso

theorem hl (x : LocallyDiscrete Limits.WalkingCospan) : @CategoryStruct.id BiWalkingCospan (locallyDiscreteBicategory Limits.WalkingCospan).toCategoryStruct x = @Discrete.mk (x.as ⟶ x.as) (𝟙 x.as) := by
  exact rfl

-- def Bicategory.pullback.Conemk {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c d: C}
--   (g : a ⟶ b) (r : c ⟶ b) (t : d ⟶ c) (l : d ⟶ a) (h1 : l ≫ g ≅ t ≫ r ) (h2 : ∀(iso : l ≫ g ≅ t ≫ r), iso = h1) : Bicategory.Cone (Bicategory.pullback.Diagrammk g r) where
--     pt := d
--     π := by
--       fconstructor
--       . rintro ⟨cs⟩
--         exact Option.casesOn cs (l ≫ g) (fun cs => Limits.WalkingPair.casesOn cs l t)
--       . rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨j⟩ <;> cases j <;> simp[Diagrammk,LaxFunctor.Const] <;> try {exact 𝟙 _}
--         . exact h1.hom
--       . rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨m1⟩ ⟨m2⟩ ⟨⟨η⟩⟩ <;> cases m1 <;> cases η <;> simp[Diagrammk,LaxFunctor.Const,Disc]
--       . rintro (⟨⟩ | ⟨⟨⟩⟩)
--         . simp [hl,Diagrammk,LaxFunctor.Const,Bicategory.Strict.leftUnitor_eqToIso,Bicategory.Strict.rightUnitor_eqToIso]
--       . sorry

abbrev Bicategory.pullback.of {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} (f : a ⟶ b) (g : c ⟶ b) :=
  Bicategory.pullback (Bicategory.pullback.Diagrammk f g)

def Bicategory.pullback.pt {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} {f : a ⟶ b} {g : c ⟶ b} (pb : Bicategory.pullback.of f g) : C :=
  pb.cone.pt

def Bicategory.pullback.fst {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} {f : a ⟶ b} {g : c ⟶ b} (pb : Bicategory.pullback.of f g) : Bicategory.pullback.pt pb ⟶ a :=
  pb.cone.π.app {as := Limits.WalkingCospan.left}

def Bicategory.pullback.snd {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} {f : a ⟶ b} {g : c ⟶ b} (pb : Bicategory.pullback.of f g) : Bicategory.pullback.pt pb ⟶ c :=
  pb.cone.π.app {as := Limits.WalkingCospan.right}

-- def Bicategory.pullback.com {C : Type v} [Bicategory C] [Bicategory.Strict C] {a b c : C} {f : a ⟶ b} {g : c ⟶ b}
--   (pb : Bicategory.pullback.of f g) :  (Bicategory.pullback.fst pb) ≫ f = (Bicategory.pullback.snd pb) ≫ g := by
--     simp [of,Diagrammk] at pb
--     simp[fst,snd,cone]
