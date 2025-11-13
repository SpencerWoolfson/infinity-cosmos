import Mathlib.AlgebraicTopology.Quasicategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Basic
import InfinityCosmos.ForMathlib.InfinityCosmos.Goals
import InfinityCosmos.BiCategoryTheory.BiCategoryLimits
import InfinityCosmos.BiCategoryTheory.SSetAlternative

universe u

open CategoryTheory

#check SSet.QCat
#check QCat.strictBicategory

open Simplicial

open SimplicialCategory

def SimpSetFull (n : Nat) : SSet := Δ[n + 2]

def HornInc (n : Nat) (i : Fin (n+3)): SSet.Category.Hom Λ[n + 2, i].toSSet Δ[n + 2].toSSet := by
  fconstructor
  fconstructor
  fconstructor
  . let f :=  Λ[n + 2, i].ι
    intros c h
    exact f.app c
  . intros c d f a
    simp

structure Inner {A B : SSet.{u}} (f : SSet.Bicategory.Hom A  B) : Prop where
  hornFilling'' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : SSet.Bicategory.Hom (Λ[n+2, i] : SSet.{u}) A)
    (_h0 : 0 < i) (_hn : i < Fin.last (n+2))(σ₁ : SSet.Bicategory.Hom Δ[n+2] B) (_hc : σ₀ ≫ f = (HornInc.{u} n i) ≫ σ₁),
    ∃ σ : SSet.Bicategory.Hom Δ[n+2] A, (σ₀ = (HornInc.{u} n i) ≫ σ) ∧ (σ₁ = σ ≫ f)


theorem Inner.pullback {a b c : SSet.{u}} (f : a ⟶ b) (g : c ⟶ b) (h : Inner f) (pb : @Limits.PullbackCone _ SSet.Category _ _ _ f g) (pbh : Limits.IsLimit pb): Inner (pb.snd) where
  hornFilling'' {n i} σ₀ h0 hn σ₁ hc := by
    have h'' : (σ₀ ≫ Limits.pullback.fst f g) ≫ f = Λ[n + 2, i].ι ≫ σ₁ ≫ g := by
      rw [Category.assoc,Limits.pullback.condition,<-Category.assoc,hc,Category.assoc]
    let h' := h.hornFilling'' (σ₀ ≫ (Limits.pullback.fst f g)) h0 hn (σ₁ ≫ g) h''
    rcases h' with ⟨e,cond⟩
    fconstructor
    . exact Limits.pullback.lift e σ₁ cond.2.symm
    . refine ⟨?_,?_⟩
      . apply Limits.pullback.hom_ext
        . simp[cond.1]
        . simp [hc]
      . simp

-- theorem Inner.pullback {a b c : SSet} (f : SSet.Bicategory.Hom a b) (g : SSet.Bicategory.Hom c b) (h : Inner f) (pb : pullback.of f g): Inner (pb.snd) where
--   hornFilling'' {n i} σ₀ h0 hn σ₁ hc := by
--     have h'' : (σ₀ ≫ pb.fst) ≫ f = (HornInc.{u_1,u_1} n i) ≫ σ₁ ≫ g := by
--       rw [Bicategory.Strict.assoc]
--       unfold Bicategory.pullback.fst
--       unfold pb.cone.π.app
--     let h' := h.hornFilling'' (σ₀ ≫ (Limits.pullback.fst f g)) h0 hn (σ₁ ≫ g) h''
--     rcases h' with ⟨e,cond⟩
--     fconstructor
--     . exact Limits.pullback.lift e σ₁ cond.2.symm
--     . refine ⟨?_,?_⟩
--       . apply Limits.pullback.hom_ext
--         . simp[cond.1]
--         . simp [hc]
--       . simp




-- theorem Inner.pullback {a b c : SSet} (f : a ⟶ b) (g : c ⟶ b) (h : Inner f) : Inner (Limits.pullback.snd f g) where
--   hornFilling'' {n i} σ₀ h0 hn σ₁ hc := by
--     have h'' : (σ₀ ≫ Limits.pullback.fst f g) ≫ f = Λ[n + 2, i].ι ≫ σ₁ ≫ g := by
--       rw [Category.assoc,Limits.pullback.condition,<-Category.assoc,hc,Category.assoc]
--     let h' := h.hornFilling'' (σ₀ ≫ (Limits.pullback.fst f g)) h0 hn (σ₁ ≫ g) h''
--     rcases h' with ⟨e,cond⟩
--     fconstructor
--     . exact Limits.pullback.lift e σ₁ cond.2.symm
--     . refine ⟨?_,?_⟩
--       . apply Limits.pullback.hom_ext
--         . simp[cond.1]
--         . simp [hc]
--       . simp

#check QCat.Bicategory.toQuiver

#check catToReflQuiver.toQuiver

-- theorem Inner.pullback' {a b c : SSet.QCat} (f : a ⟶ b) (g : c ⟶ b) (h : Inner' g) (pb : Bicategory.pullback.of f g): @Inner' pb.pt a (@Bicategory.pullback.fst SSet.QCat _ _ a b c _ _ pb) where
