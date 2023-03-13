{-# OPTIONS --sized-types #-}

open import SortedAlgebra
open import CounterpartModel

module Semantics {ℓ} {Σ : Signature {ℓ}} (M : CounterpartModel Σ) where --(M : CounterpartModel Σ) where

open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Relation.Unary using (_∈_; Pred)
open import Relation.Nullary using (¬_; Dec)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; isEquivalence; sym; trans; cong; cong-app; cong₂)

open Signature Σ
open SortedAlgebra.Term Σ
open import QLTL Σ

open import Predicates

open CounterpartModel.CounterpartModel M

infix 10 _,_⊨_

mutual
  at∃ : ∀ {n} {Γ : Ctx n} {ω}
      → (σ : CounterpartTrace M ω)
      → Assignment Γ (d ω)
      → QLTL Γ
      → Pred ℕ ℓ
  at∃ σ μ ϕ i = ∃[ μ′ ] (lift (C≤ i σ) μ μ′ × skip i σ , μ′ ⊨ ϕ)

  at∀ : ∀ {n} {Γ : Ctx n} {ω}
      → (σ : CounterpartTrace M ω)
      → Assignment Γ (d ω)
      → QLTL Γ
      → Pred ℕ ℓ
  at∀ σ μ ϕ i = ∀ μ′ → lift (C≤ i σ) μ μ′ → skip i σ , μ′ ⊨ ϕ

  _,_⊨_ : ∀ {n} {Γ : Ctx n} {ω}
        → (σ : CounterpartTrace M ω)
        → Assignment Γ (d ω)
        → QLTL Γ
        → Set ℓ
  σ , μ ⊨ true     = ⊤
  σ , μ ⊨ false    = ⊥
  σ , μ ⊨ ! ϕ      = ¬ (σ , μ ⊨ ϕ)
  σ , μ ⊨ ϕ₁ ∧ ϕ₂  = σ , μ ⊨ ϕ₁ × σ , μ ⊨ ϕ₂
  σ , μ ⊨ ϕ₁ ∨ ϕ₂  = σ , μ ⊨ ϕ₁ ⊎ σ , μ ⊨ ϕ₂
  σ , μ ⊨ ∃< τ > ϕ = ∃[ a ] σ , ⟨ a , μ ⟩ ⊨ ϕ
  σ , μ ⊨ ∀< τ > ϕ =  ∀ a → σ , ⟨ a , μ ⟩ ⊨ ϕ
  σ , μ ⊨ t₁ ≡ᵗ t₂ = interpret (d _) μ t₁ ≡ interpret (d _) μ t₂
  σ , μ ⊨ t₁ ≢ᵗ t₂ = interpret (d _) μ t₁ ≢ interpret (d _) μ t₂
  σ , μ ⊨ O ϕ      = ∃[ μ₁ ] lift (Σ-rel σ) μ μ₁ × tail σ , μ₁ ⊨ ϕ
  σ , μ ⊨ A ϕ      = ∀  μ₁ → lift (Σ-rel σ) μ μ₁ → tail σ , μ₁ ⊨ ϕ
  σ , μ ⊨ ϕ₁ U ϕ₂  = at∃ σ μ ϕ₁ until at∃ σ μ ϕ₂
  σ , μ ⊨ ϕ₁ F ϕ₂  = at∀ σ μ ϕ₁ until at∀ σ μ ϕ₂
  σ , μ ⊨ ϕ₁ W ϕ₂  = at∃ σ μ ϕ₁ weakUntil at∃ σ μ ϕ₂
  σ , μ ⊨ ϕ₁ T ϕ₂  = at∀ σ μ ϕ₁ weakUntil at∀ σ μ ϕ₂

TraceDecidableFormula : ∀ {n} {Γ : Ctx n} {ω}
                 → (σ : CounterpartTrace M ω)
                 → QLTL Γ
                 → Set ℓ
TraceDecidableFormula {_} {Γ} {ω} σ ϕ =
  ∀ i (μ : Assignment Γ (d (wi i σ))) → Dec (skip i σ , μ ⊨ ϕ)
