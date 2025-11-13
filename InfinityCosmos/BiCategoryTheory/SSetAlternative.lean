import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import InfinityCosmos.ForMathlib.InfinityCosmos.Goals
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

universe v v' u u'
namespace CategoryTheory
namespace SimplicialCategory

section

noncomputable def SSet.SimplicialCat : SimplicialCategory SSet where
 Hom X Y := X.functorHom Y
 id X := Functor.natTransEquiv.symm (𝟙 X)
 comp X Y Z := { app := fun _ ⟨f, g⟩ => f.comp g }
 homEquiv := Functor.natTransEquiv.symm

noncomputable instance SSet.SSetEnrichedCat : EnrichedOrdinaryCategory SSet SSet := by
  let t := SSet.SimplicialCat
  unfold SimplicialCategory at t
  exact t

noncomputable instance SSet.CatEnrichedCat : EnrichedCategory Cat SSet :=
  instEnrichedCategoryTransportEnrichment (C := SSet) SSet.hoFunctor

noncomputable instance SSet.Bicategory : Bicategory SSet := inferInstance
-- noncomputable instance SSet.Category : Category SSet := StrictBicategory.category SSet

def BiSSet : Type (u + 1) := SimplicialObject (Type u)

noncomputable instance BiSSet.Bicategory : Bicategory BiSSet := by
  let h := SSet.Bicategory
  unfold SSet at h
  unfold BiSSet
  exact h

noncomputable instance BiSSet.StrictBicategory : Bicategory.Strict BiSSet := by
  let h : Bicategory.Strict SSet := by exact instStrict_infinityCosmos SSet
  unfold SSet at h
  unfold BiSSet
  exact h

noncomputable instance BiSSet.Category : Category BiSSet := StrictBicategory.category BiSSet


-- noncomputable def BiSSetToSSet : Pseudofunctor BiSSet SSet where
--   obj X := X
--   map {X Y} f := by
--     exact f
--   map₂ {a b f g η} := by
--     exact η
--   mapId X := by
--     exact bicategoricalIso (𝟙 X) (𝟙 X)
--   mapComp := by
--     exact fun {a b c} f g ↦ bicategoricalIso (f ≫ g) (f ≫ g)



noncomputable def BiSSetToPsh : BiSSet.{u} ⥤ (SimplexCategoryᵒᵖ ⥤ (Type u)) where
  obj X := X
  map {X Y} f := by
    unfold Quiver.Hom at f
    dsimp [BiSSet.Category,StrictBicategory.category,BiSSet.Bicategory,SSet.Bicategory,inferInstance,instBicategory_infinityCosmos,SSet.CatEnrichedCat] at f
    unfold EnrichedCategory.Hom at f
    unfold BiSSet at X Y
    let fh : Functor.HomObj X Y (Functor.chosenTerminal _ (Type u)) := sorry
    let hh := (Functor.homObjEquiv _ _ _).toFun fh





  --   rcases f with ⟨f⟩
  --   unfold Cat.FreeRefl at f
  --   refine Quotient.recOn f ?_
  --   intro f'
  --   rcases f' with ⟨app,nat⟩
  --   fconstructor
  --   . intro c
  --     apply (app c)
  --     fconstructor
  --     refine
  --       (Opposite.unop c).const
  --         (Opposite.unop
  --           (Opposite.unop
  --             (Opposite.op
  --               ((SimplexCategory.Truncated.inclusion 2).op.obj
  --                 (Opposite.op
  --                   { obj := SimplexCategory.mk 0, property := SSet.OneTruncation₂._proof_1 })))))
  --         ?_
  --     simp [SimplexCategory.len,SimplexCategory.Truncated.inclusion,SimplexCategory.mk]
  --     exact {val := 0, isLt := by simp}
  --   . intro x y f
  --     simp
  --     let nat' := fun(a) => (nat f a).symm
  --     rw [nat']
  --     simp [SimplexCategory.const]
  --     exact rfl
  -- map_comp {X Y Z} f g := by
  --   --  refine Quotient.recOn f ?_
  --   --  intro f'
  --   --  refine Quotient.recOn g ?_
  --   --  intro g'
  --    simp [SimplexCategory.mk,SimplexCategory.const,SimplexCategory.Hom.mk]
  --    apply Quotient.sound





    -- simp [SSet.SSetEnrichedCat,SSet.SimplicialCat,EnrichedCategory.Hom,Functor.functorHom] at f'
    -- rcases f'





-- noncomputable def BiSSetToSSet : BiSSet ⥤ SSet where
--   obj X := X
--   map {X Y} f := by
--     fconstructor
--     . rcases f with ⟨f⟩
--       unfold Cat.FreeRefl at f
--       refine Quotient.recOn f ?_
--       intro f
--       intro x
--       apply f.app x
--       fconstructor
--       apply SimplexCategory.Hom.mk
--       fconstructor
--       . exact fun _ => {val := 0, isLt := by simp}
--       . exact monotone_const
--     . intro a b g
--       rcases f with ⟨⟨⟨f,nat⟩⟩⟩
--       simp
--       set h1 : Fin ((Opposite.unop a).len + 1) →o Fin (1) := { toFun := fun x ↦ 0, monotone' := _ }
--       set h2 : (Opposite.unop a ⟶ (SimplexCategory.Truncated.inclusion 2).obj { obj := SimplexCategory.mk 0, property := SSet.OneTruncation₂._proof_1 })ᵒᵖ := (Opposite.op _)
--       let sol := nat g h2
--       rw [<- sol]
--       simp [h2]
--       congr
--   map_id X := by
--     ext n a
--     exact rfl
--   map_comp {X Y Z} f g := by
--     refine SSet.hom_ext ?_
--     intro n
--     rcases f with ⟨⟨⟨f,_⟩⟩⟩
--     rcases g with ⟨⟨⟨g,_⟩⟩⟩
--     simp [SimplexCategory,SimplexCategory.Hom.mk]
--     unfold CategoryStruct.comp
--     simp [BiSSet.Category,StrictBicategory.category,BiSSet.Bicategory,SSet.Bicategory,inferInstance,instBicategory_infinityCosmos,eComp,EnrichedCategory.comp,SSet.hoFunctor]
--     simp [SSet.Truncated.hoFunctor₂,SSet.Truncated.mapHomotopyCategory,Functor.comp]


#check Cat.FreeRefl.quotientFunctor

noncomputable def SSetToBiSSet : SSet.{u} ⥤ BiSSet.{u} where
  obj X := X
  map { X Y } f := by
    fconstructor
    apply (Cat.FreeRefl.quotientFunctor (SSet.OneTruncation₂ ((SSet.truncation 2).obj (EnrichedCategory.Hom X Y)))).obj
    rcases f with ⟨fapp,fnat⟩
    fconstructor
    . intro c h
      apply fapp
    . intro c d f a
      apply fnat
  map_id X := rfl
  map_comp {X Y Z} f g := by
    rcases f with ⟨f⟩
    rcases g with ⟨g⟩
    simp[Cat.FreeRefl.quotientFunctor,CategoryStruct.comp]
    set hh : Quotient SSet.Truncated.HoRel₂ := {as := (Quotient.functor Cat.FreeReflRel).obj { app := fun c h ↦ g c, naturality := _ }}










noncomputable def BiSSetIsoSSet : BiSSet.{u} ≌ SSet.{u} := by
  unfold SSet BiSSet SimplicialObject
  apply Equivalence.mk



  -- functor := BiSSetToSSet
  -- inverse := SSetToBiSSet
  -- unitIso := by
  --   fconstructor
  --   . exact 𝟙 (𝟭 BiSSet)
  --   . exact 𝟙 (BiSSetToSSet ⋙ SSetToBiSSet)
  --   . exact Category.id_comp (𝟙 (BiSSetToSSet ⋙ SSetToBiSSet))
  --   . exact Category.id_comp (𝟙 (𝟭 BiSSet))
  -- counitIso := by
  --   fconstructor
  --   . exact 𝟙 (BiSSetToSSet ⋙ SSetToBiSSet)
  --   . exact 𝟙 (𝟭 BiSSet)
  --   . exact Category.id_comp (𝟙 (𝟭 BiSSet))
  --   . exact Category.id_comp (𝟙 (BiSSetToSSet ⋙ SSetToBiSSet))

-- noncomputable def SSetToPrsh : SSet.{u} ⥤ (SimplexCategoryᵒᵖ ⥤ Type u) where
--   obj X := by
--     exact X
--   map {X Y} f := by
--     dsimp [Quiver.Hom]
--     fconstructor
--     . simp [Quiver.Hom,EnrichedCategory.Hom] at f
--       intro Xx
--       rcases f with ⟨⟨⟨f⟩⟩⟩
--       apply f Xx
--       simp
--       fconstructor
--       simp [Quiver.Hom,SimplexCategory.Hom,SimplexCategory.Truncated.inclusion]
--       fconstructor
--       . exact fun _ => {val := 0, isLt := by simp}
--       . exact monotone_const
--     . intros a b g
--       simp
--       cases f
--       rename_i as
--       simp at as
--       rcases as with ⟨⟨as,n⟩⟩
--       simp [Quotient.rec]
--       set s1 : Fin ((Opposite.unop a).len + 1) →o Fin 1 := { toFun := fun x ↦ 0, monotone' := _}
--       set s2 := (Opposite.op (id s1))
--       let ng := n g
--       apply ng s2






-- noncomputable def PrshToSSet : (SimplexCategoryᵒᵖ ⥤ Type u) ⥤ SSet.{u} where
--   obj X := X
--   map f := f

-- noncomputable def SSetIsoPsh : SSet ≌ SSet where
--   functor := SSetToPrsh
--   inverse := PrshToSSet
--   unitIso := sorry
--   counitIso := sorry

def EquivPreservesHasLimits {C D: Type u} [Category.{v} C] [Category.{v} D] (eq : C ≌ D) [l : Limits.HasLimits C] : Limits.HasLimits D := by
  refine { has_limits_of_shape := ?_ }
  intro J Jc
  refine { has_limit := ?_ }
  intro F
  let hh1 : Limits.HasLimit (F ⋙ eq.inverse) := by
    let h1 := l.has_limits_of_shape J
    exact Limits.hasLimitOfHasLimitsOfShape (F ⋙ eq.inverse)
  let hh2 : Limits.HasLimit ((F ⋙ eq.inverse) ⋙ eq.functor) := by
    exact Limits.instHasLimitCompOfPreservesLimit
  refine (Limits.hasLimit_iff_of_iso ?_).mpr hh2
  rw [Functor.assoc]
  nth_rw 1 [<- CategoryTheory.Functor.comp_id F]
  refine NatIso.hcomp ?_ ?_
  . exact Iso.refl F
  . exact eq.counitIso.symm

#check SSet.hasLimits


noncomputable instance : Limits.HasLimits SSet.{u} := by
  let hl := SSet.hasLimits.{u}
  simp[SSet.largeCategory] at hl
  apply SSet.hasLimits.{u}



noncomputable instance : Limits.HasLimits BiSSet := EquivPreservesHasLimits BiSSetIsoSSet.symm

end

section
variable (B : Type u) [bc : Bicategory B] (P : B → Prop)

def SubBiCat : Type u := (b : B) ×' (P b)

instance SubBiCat.BiCat : Bicategory (SubBiCat B P) where
  Hom x y := x.fst ⟶ y.fst
  id x := 𝟙 x.fst
  comp f g := f ≫ g
  whiskerLeft f g h η := Bicategory.whiskerLeft f η
  whiskerRight η h := Bicategory.whiskerRight η h
  associator f g h := Bicategory.associator f g h
  leftUnitor f := Bicategory.leftUnitor f
  rightUnitor g := Bicategory.rightUnitor g
  whisker_exchange η θ := by
    simp [bc.whisker_exchange η θ]

instance SubBiCat.BiCatStrict [bs : Bicategory.Strict B]: Bicategory.Strict (SubBiCat B P) where
  id_comp f := by
    simp [Quiver.Hom] at f
    exact bs.id_comp f
  comp_id f := by
    simp [Quiver.Hom] at f
    exact bs.comp_id f
  assoc f g h := by
    simp [Quiver.Hom] at f
    exact bs.assoc f g h
  leftUnitor_eqToIso f := by
    simp [Quiver.Hom] at f
    exact bs.leftUnitor_eqToIso f
  rightUnitor_eqToIso f := by
    simp [Quiver.Hom] at f
    exact bs.rightUnitor_eqToIso f
  associator_eqToIso f := by
    simp [Quiver.Hom] at f
    exact bs.associator_eqToIso f

end


-- section



-- noncomputable instance BiSSet.Bicategory : Bicategory BiSSet.{u} := by
--   unfold BiSSet
--   apply?

-- def BiSSet.Hom (X Y : BiSSet) : Type* := (SSet.hoFunctor.obj (X.functorHom Y)).α

-- def BiSSet.Hom.toNatTrans {X Y : BiSSet.{u}} (f : BiSSet.Hom.{u} X Y) : NatTrans X Y where
--   app n := by
--     rcases f with ⟨⟨⟨f,_⟩⟩⟩
--     apply f n
--     simp [Quiver.Hom,SimplexCategory.Hom]
--     fconstructor
--     fconstructor
--     . intro m
--       simp[SimplexCategory.len,SimplexCategory.Truncated.inclusion,SimplexCategory.mk]
--       exact {val := 0, isLt := by simp}
--     . exact monotone_const
--   naturality n m s := by
--     rcases f with ⟨⟨⟨f,nat⟩⟩⟩
--     set a1 := @OrderHom.mk ..
--     set a1' := @OrderHom.mk ..
--     set a2 := (Opposite.op a1')
--     set a3 := by
--       refine @id (Opposite.op ((SimplexCategory.Truncated.inclusion 2).obj { obj := SimplexCategory.mk 0, property := SSet.OneTruncation₂._proof_1 }) ⟶ n) ?_
--       simp [Quiver.Hom,SimplexCategory.Hom]
--       exact a2
--     let nat' := nat s a3
--     simp [a3] at nat'
--     simp
--     rw [<- nat']
--     refine X.map s ≫= ?_
--     apply congr
--     . simp
--     . simp[a2,a1,a1']
--       exact eq_of_comp_right_eq fun {X} ↦ congrFun rfl

-- def BiSSet.Hom.fromNatTrans {X Y : BiSSet.{u}} (f : NatTrans X Y) : BiSSet.Hom X Y := by
--   fconstructor
--   fconstructor
--   fconstructor
--   . intro n _
--     exact f.app n
--   . intro _ _ _ _
--     (expose_names; exact f.naturality f_1)








-- noncomputable instance BiSSet.Hom.Cat (X Y : BiSSet) : Category (BiSSet.Hom X Y) := (SSet.hoFunctor.obj (X.functorHom Y)).str

-- noncomputable instance BiSSet.Bicategory : Bicategory BiSSet.{u} where
--   Hom X Y := BiSSet.Hom X Y
--   id X := BiSSet.Hom.fromNatTrans (NatTrans.id X)
--   comp {X Y Z} f g := by
--     exact BiSSet.Hom.fromNatTrans (NatTrans.vcomp (BiSSet.Hom.toNatTrans f) (BiSSet.Hom.toNatTrans g))
--   whiskerLeft {a b c} f g h η := by
--     simp [Quiver.Hom,inferInstance] at η














-- def BiSSet.Hom (X Y : BiSSet) := ((X.functorHom Y).obj (Opposite.op (SimplexCategory.mk 0)))



-- def SCidMap : (Opposite.op (SimplexCategory.mk 0)) ⟶ (Opposite.op (SimplexCategory.mk 1)) := by
--   refine Quiver.Hom.op ?_
--   exact SimplexCategory.diag 0

-- def SCsorMap : (Opposite.op (SimplexCategory.mk 1)) ⟶ (Opposite.op (SimplexCategory.mk 0)) := by
--   refine Quiver.Hom.op ?_
--   refine SimplexCategory.δ ?_
--   refine {val := 0, isLt := ?_}
--   simp

-- def SCtargMap : (Opposite.op (SimplexCategory.mk 1)) ⟶ (Opposite.op (SimplexCategory.mk 0)) := by
--   refine Quiver.Hom.op ?_
--   refine SimplexCategory.δ ?_
--   refine {val := 1, isLt := ?_}
--   simp

-- def Sorce {X Y : BiSSet} (x : ((X.functorHom Y).obj (Opposite.op (SimplexCategory.mk 1)))) : BiSSet.Hom X Y := by
--   exact (X.functorHom Y).map SCsorMap x

-- def Target {X Y : BiSSet} (x : ((X.functorHom Y).obj (Opposite.op (SimplexCategory.mk 1)))) : BiSSet.Hom X Y := by
--   exact (X.functorHom Y).map SCtargMap x

-- def BiSSet.Hom.Hom' {X Y : BiSSet} (a b : BiSSet.Hom X Y) := (η : ((X.functorHom Y).obj (Opposite.op (SimplexCategory.mk 1)))) ×' (Sorce η = a) ×' (Target η = b)

-- noncomputable instance BiSSet.Hom.Category {X Y : BiSSet} : Category (BiSSet.Hom X Y) where
  -- Hom a b := BiSSet.Hom.Hom' a b
  -- id a := by
  --   refine ⟨(X.functorHom Y).map SCidMap a, ?_, ?_⟩
  --   . unfold Sorce
  --     simp [Functor.functorHom,Functor.homObjFunctor]
  --     congr
  --     ext _ x _
  --     let hh : SCidMap ≫ SCsorMap = 𝟙 _ := by
  --       simp[SCidMap,SCsorMap, <- op_id,<- op_comp]
  --       congr 1
  --       exact SimplexCategory.hom_zero_zero (SimplexCategory.δ 0 ≫ SimplexCategory.diag 0)
  --     simp [<-Category.assoc, hh]
  --   . unfold Target
  --     simp [Functor.functorHom,Functor.homObjFunctor]
  --     congr
  --     ext _ x _
  --     let hh : SCidMap ≫ SCtargMap = 𝟙 _ := by
  --       simp[SCidMap,SCtargMap, <- op_id,<- op_comp]
  --       congr 1
  --       exact SimplexCategory.hom_zero_zero (SimplexCategory.δ 1 ≫ SimplexCategory.diag 0)
  --     simp [<-Category.assoc, hh]
  -- comp {x y z} f g := by
  --   rcases f with ⟨f,fs,ft⟩
  --   rcases g with ⟨g,gs,gt⟩
  --   fconstructor
  --   . simp [Functor.functorHom] at f g





-- noncomputable instance BiSSet.HomCat (X Y : BiSSet) : Category ((X.functorHom Y).obj (Opposite.op (SimplexCategory.mk 0))) where
--   Hom a b := ((X.functorHom Y).obj (Opposite.op (SimplexCategory.mk 1)))
--   id a := by
--     let id : Opposite.op (SimplexCategory.mk 0) ⟶ Opposite.op (SimplexCategory.mk 1) := by
--       refine Quiver.Hom.op ?_
--       exact SimplexCategory.diag 0
--     let id' := (Functor.functorHom X Y).map id
--     exact id' a
--   comp f g := by
--     simp [Functor.functorHom]



-- noncomputable def SSet.SimplicialCat : SimplicialCategory SSet where
--  Hom X Y := X.functorHom Y
--  id X := Functor.natTransEquiv.symm (𝟙 X)
--  comp X Y Z := { app := fun _ ⟨f, g⟩ => f.comp g }
--  homEquiv := Functor.natTransEquiv.symm

-- noncomputable instance SSet.SSetEnrichedCat : EnrichedOrdinaryCategory SSet SSet := by
--   let t := SSet.SimplicialCat
--   unfold SimplicialCategory at t
--   exact t

-- noncomputable instance SSet.CatEnrichedCat : EnrichedCategory Cat SSet :=
--   instEnrichedCategoryTransportEnrichment (C := SSet) SSet.hoFunctor

-- noncomputable instance SSet.Bicategory : Bicategory SSet := inferInstance
-- noncomputable instance SSet.Category : Category SSet := StrictBicategory.category SSet

-- def BiQCat : Type (u+1) := SubBiCat SSet SSet.Quasicategory

-- noncomputable instance : Bicategory BiQCat := SubBiCat.BiCat SSet SSet.Quasicategory
-- noncomputable instance : Bicategory.Strict BiQCat := SubBiCat.BiCatStrict SSet SSet.Quasicategory
-- noncomputable instance : Category BiQCat := StrictBicategory.category BiQCat

-- section
-- /- This is Code stolen from the Goals File. I do not want to import it because it contains some
-- Stuff I do not want.-/

-- instance DiscretePUnit.isTerminal : Limits.IsTerminal (Cat.of (Discrete PUnit)) :=
--   Limits.IsTerminal.ofUniqueHom (fun C ↦ star C) (fun _ _ => punit_ext' _ _)

-- noncomputable def finOneTerminalIso : ⊤_ Cat.{u,u} ≅ Cat.of (Discrete.{u} PUnit) :=
--   Limits.terminalIsoIsTerminal DiscretePUnit.isTerminal

-- noncomputable def hoFunctor.terminalIso : (SSet.hoFunctor.obj (⊤_ SSet)) ≅ (⊤_ Cat) :=
--   SSet.hoFunctor.mapIso (terminalIsoIsTerminal isTerminalDeltaZero) ≪≫
--     SSet.hoFunctor.mapIso (simplexIsNerve 0) ≪≫
--     nerveFunctorCompHoFunctorIso.app (Cat.of (ULiftFin 1)) ≪≫
--     ULiftFinDiscretePUnitIso ≪≫ finOneTerminalIso.symm

-- instance hoFunctor.preservesTerminal : Limits.PreservesLimit (Functor.empty.{0} SSet) SSet.hoFunctor :=
--   Limits.preservesTerminal_of_iso SSet.hoFunctor hoFunctor.terminalIso

-- instance hoFunctor.preservesTerminal' :
--     Limits.PreservesLimitsOfShape (Discrete PEmpty.{1}) SSet.hoFunctor :=
--   Limits.preservesLimitsOfShape_pempty_of_preservesTerminal _

-- instance hoFunctor.preservesFiniteProducts : Limits.PreservesFiniteProducts SSet.hoFunctor :=
--   Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

-- noncomputable instance hoFunctor.laxMonoidal :  SSet.hoFunctor.LaxMonoidal :=
--   (Functor.Monoidal.ofChosenFiniteProducts SSet.hoFunctor).toLaxMonoidal

-- noncomputable instance SSet.CatEnrichedCat : EnrichedCategory Cat SSet :=
--   instEnrichedCategoryTransportEnrichment (C := SSet) SSet.hoFunctor
-- end
