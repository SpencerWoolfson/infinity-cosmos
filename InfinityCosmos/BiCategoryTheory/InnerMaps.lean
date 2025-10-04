import Mathlib.AlgebraicTopology.Quasicategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Basic
import InfinityCosmos.ForMathlib.InfinityCosmos.Goals
import InfinityCosmos.BiCategoryTheory.BiCategoryLimits

open CategoryTheory

#check SSet.QCat
#check QCat.strictBicategory

open Simplicial

structure Inner {A B : SSet} (f : A ⟶ B) : Prop where
  hornFilling'' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : (Λ[n+2, i] : SSet) ⟶ A)
    (_h0 : 0 < i) (_hn : i < Fin.last (n+2))(σ₁ : Δ[n+2] ⟶ B) (_hc : σ₀ ≫ f = Λ[n + 2, i].ι ≫ σ₁),
    ∃ σ : Δ[n+2] ⟶ A, (σ₀ = Λ[n + 2, i].ι ≫ σ)∧(σ₁ = σ ≫ f)

theorem Inner.pullback {a b c : SSet} (f : a ⟶ b) (g : c ⟶ b) (h : Inner f) : Inner (Limits.pullback.snd f g) where
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

theorem Inner.pullback' {a b c : SSet.QCat} (f : a ⟶ b) (g : c ⟶ b) (h : Inner f) : Inner (Bicategory.pullbackOf f g).map  where