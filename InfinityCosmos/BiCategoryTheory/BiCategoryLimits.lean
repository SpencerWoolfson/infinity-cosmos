import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Bicategory.Functor.Lax
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

open CategoryTheory

def Bicategory.Terminal {C : Type} [Bicategory C] [Bicategory.Strict C] (x : C) : Prop
  := ∀(y : C), ∃(f : y ⟶ x), ∀(g : y ⟶ x), ∃(iso : f ≅ g), ∀(iso' : f ≅ g), iso = iso'

def Bicategory.LaxFunctor.Const (C : Type) {D : Type} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] (x : D) : OplaxFunctor C D where
    obj _ := x
    map _ := 𝟙 x
    map₂ _ := 𝟙 (𝟙 x)
    mapId _ := 𝟙 (𝟙 x)
    mapComp _ _ := eqToHom (Category.comp_id (𝟙 x)).symm
    map₂_associator := by simp[Bicategory.Strict.associator_eqToIso]
    map₂_leftUnitor := by simp[Bicategory.Strict.leftUnitor_eqToIso]
    map₂_rightUnitor := by simp[Bicategory.Strict.rightUnitor_eqToIso]

structure Bicategory.Cone {C : Type} {D : Type} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] (F : OplaxFunctor C D) where
   pt : D
   π : Oplax.OplaxTrans (Bicategory.LaxFunctor.Const C pt) F

def Bicategory.ConstNT (C : Type) {D : Type} [Bicategory C] [Bicategory.Strict C]
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

structure Bicategory.Cone.Hom {C : Type} {D : Type} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] {F : OplaxFunctor C D} (A B : Bicategory.Cone F) where
    map : A.pt ⟶ B.pt
    nat : A.π = Oplax.OplaxTrans.vcomp (Bicategory.ConstNT C map) B.π

structure Bicategory.Lim {C : Type} {D : Type} [Bicategory C] [Bicategory.Strict C]
  [Bicategory D] [Bicategory.Strict D] (F : OplaxFunctor C D) where
    cone : Bicategory.Cone F
    exis (c : Bicategory.Cone F): Bicategory.Cone.Hom c cone
    uniq (c : Bicategory.Cone F) (f : Bicategory.Cone.Hom c cone) : f.map ≅ (exis c).map
    uniq_uniq (c : Bicategory.Cone F) (f : Bicategory.Cone.Hom c cone) (iso : f.map ≅ (exis c).map) : uniq c f = iso

abbrev BiWalkingCospan := CategoryTheory.LocallyDiscrete Limits.WalkingCospan

-- def BiPullBackCone {C : Type} [Bicategory C] [Bicategory.Strict C] {x y z : C} (f : x ⟶ y) (g : z ⟶ y) : OplaxFunctor (BiWalkingCospan) C where
--   obj x := by
--     rcases x with ⟨x⟩
--     cases x
--     . exact y
--     . rename_i x
--       cases x
--       . exact x
--       exact y
--   map {a b} h := by
--     rcases a with ⟨a⟩
--     rcases b with ⟨b⟩
--     rcases h with ⟨h⟩
--     cases a <;> cases b <;> simp
--     . exact 𝟙 y
--     . rename_i b
--       cases b
--       . simp at h
--         contradiction
--       . simp at h
--         contradiction
--     . rename_i a
--       cases a
--       . simp
--         exact f
--       . simp
--         exact 𝟙 y
--     . rename_i a b
--       cases a <;> cases b <;> simp
--       . exact 𝟙 x
--       . exact f
--       . simp at h
--         contradiction
--       . exact 𝟙 y
--   map₂ η := by
--     simp[Discrete.rec]








structure Bicategory.pullback {C : Type} [Bicategory C] [Bicategory.Strict C] (F : OplaxFunctor (BiWalkingCospan) C) where
  cone : Bicategory.Cone F
  ump : Bicategory.Lim F

-- instance : Category BiWalkingCospan where
--   Hom X Y := by
--     unfold BiWalkingCospan at X Y
--     exact Discrete (X ⟶ Y)
--   id X := by
--     unfold BiWalkingCospan at X
--     refine { as := 𝟙 X}
--   comp {X Y Z} f g := by
--     unfold BiWalkingCospan at X Y Z
--     refine { as := f.as ≫ g.as}

-- instance : Bicategory BiWalkingCospan where
--   homCategory a b := by
--     apply discreteCategory
--   whiskerLeft {a b c} f {g h} i := by
--     fconstructor
--     refine { down := ?_ }
--     refine Discrete.ext_iff.mp ?_
--     unfold BiWalkingCospan at a b c

--     apply?








-- instance Bicategory.Cone.Cat {C : Type} {D : Type} [Bicategory C] [Bicategory.Strict C]
--   [Bicategory D] [Bicategory.Strict D] (F : OplaxFunctor C D) : Bicategory (Bicategory.Cone F) where
--     Hom A B := Bicategory.Cone.Hom A B
--     comp {X Y Z} f g := by
--       fconstructor
--       . refine f.map ≫ g.map
--       . rw [f.nat,g.nat]
--         simp [ConstNT,Oplax.OplaxTrans.vcomp,Bicategory.Strict.associator_eqToIso]
--         refine Function.hfunext rfl ?_
--         intro a _ h
--         cases (eq_of_heq h)
--         refine Function.hfunext rfl ?_
--         intro c _ h
--         cases (eq_of_heq h)
--         refine Function.hfunext rfl ?_
--         intro f _ h
--         apply (eqToHom_comp_heq_iff _ _ _).mpr
--         apply (comp_eqToHom_heq_iff _ _ _).mpr
--         apply (heq_eqToHom_comp_iff _ _ _).mpr
--         apply (heq_comp_eqToHom_iff _ _ _).mpr
--         cases h
--         exact Quiver.heq_of_homOfEq_ext rfl rfl rfl
--     id x := by
--       fconstructor
