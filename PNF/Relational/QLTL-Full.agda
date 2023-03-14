{-# OPTIONS --guardedness #-}

module PNF.Relational.QLTL-Full where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Unary hiding (U)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import PNF.QLTL-Full public
open import PNF.Relational.Counterpart
open import VecT
open import Predicates

-- Counterpart semantics of extended QLTL full with all derived operators
infix 10 _,_⊨_

_,_⊨_ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL-Full n → Set
σ , μ ⊨ true = ⊤
σ , μ ⊨ false = ⊥
σ , μ ⊨ ! ϕ = ¬ σ , μ ⊨ ϕ
σ , μ ⊨ x == y = μ [ x ] ≡ μ [ y ]
σ , μ ⊨ x != y = μ [ x ] ≢ μ [ y ]
σ , μ ⊨ (ϕ₁ ∧ ϕ₂) = σ , μ ⊨ ϕ₁ × σ , μ ⊨ ϕ₂
σ , μ ⊨ (ϕ₁ ∨ ϕ₂) = σ , μ ⊨ ϕ₁ ⊎ σ , μ ⊨ ϕ₂
σ , μ ⊨ (∃<> ϕ) = ∃[ x ] σ , (x , μ) ⊨ ϕ
σ , μ ⊨ (∀<> ϕ) = ∀ x → σ , (x , μ) ⊨ ϕ
σ , μ ⊨ (◯ ϕ) = ∃C∈ ↑ (C≤ 1 σ) μ ⇒ (s 1 σ ,_⊨ ϕ)
σ , μ ⊨ (A ϕ) = ∀C∈ ↑ (C≤ 1 σ) μ ⇒ (s 1 σ ,_⊨ ϕ)
σ , μ ⊨ (ϕ₁ U ϕ₂)  = (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) until     (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ F ϕ₂)  = (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) until     (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ W ϕ₂)  = (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) weakUntil (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ T ϕ₂)  = (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) weakUntil (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
