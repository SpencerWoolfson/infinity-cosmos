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

universe v v' u u'
namespace CategoryTheory
namespace SimplicialCategory

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
noncomputable instance SSet.Category : Category SSet := StrictBicategory.category SSet

def BiQCat : Type (u+1) := SubBiCat SSet SSet.Quasicategory

noncomputable instance : Bicategory BiQCat := SubBiCat.BiCat SSet SSet.Quasicategory
noncomputable instance : Bicategory.Strict BiQCat := SubBiCat.BiCatStrict SSet SSet.Quasicategory
noncomputable instance : Category BiQCat := StrictBicategory.category BiQCat

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
