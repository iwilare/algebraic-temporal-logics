{-# OPTIONS --sized-types #-}

open import SortedAlgebra
open import CounterpartModel

module Semantics {ℓ} {Σ : Signature {ℓ}} (M : CounterpartModel Σ) where --(M : CounterpartModel Σ) where

open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Relation.Unary using (_∈_)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; isEquivalence; sym; trans; cong; cong-app; cong₂)

open Signature Σ
open SortedAlgebra.Term Σ
open import QLTL Σ

open CounterpartModel.CounterpartModel M

infix 10 _,_⊨_

-- Shorthand for:
--   "There exists a counterpart for s in the
--    path p after i steps which satisfies A"
at∃ : ∀ {ω} → X.₀ ω → ClassicalAttribute X → ℕ → Set _
at∃ s A i = ∃[ z ] X.₁ (compose≤ p i) z s × z ∈ A
--
---- Shorthand for:
----   "All counterparts of s in the path p
----    after i steps satisfy A"
--at∀ : ∀ {ω} → X.₀ ω → ClassicalAttribute X → ℕ → Set _
--at∀ p s A i = ∀ z → X.₁ (compose≤ p i) z s → z ∈ A

{-
XO : ClassicalAttribute X → ClassicalAttribute X
XO A s = ∀ {σ}
        → (ρ : _ ⇒ σ)
        → {ρ ∈ T}
        → ∃[ z ] X.₁ ρ z s × s ∈ A

XA : ClassicalAttribute X → ClassicalAttribute X
XA A s = ∀ {σ}
        → (ρ : _ ⇒ σ)
        → {ρ ∈ T}
        → ∀ z → X.₁ ρ z s → s ∈ A

XU : ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
XU A B {ω} s = ∀ (p : Path ω ∞) → (at∃ p s A) until (at∃ p s B)

XF : ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
XF A B {ω} s = ∀ (p : Path ω ∞) → (at∀ p s A) until (at∀ p s B)

XW : ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
XW A B {ω} s = ∀ (p : Path ω ∞) → (at∃ p s A) weakUntil (at∃ p s B)

XT : ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
XT A B {ω} s = ∀ (p : Path ω ∞) → (at∀ p s A) weakUntil (at∀ p s B)
-}

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
σ , μ ⊨ O ϕ      = ∃[ μ₁ ] ({!   !} × {!   !}) --{!   !} --XO (⟦ _ ⟧*) ⟨ ϕ ⟩
σ , μ ⊨ A ϕ      = {!   !} --{!   !} --XA (⟦ _ ⟧*) ⟨ ϕ ⟩
σ , μ ⊨ ϕ₁ U ϕ₂  = {!   !} --{!   !} --XU (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
σ , μ ⊨ ϕ₁ F ϕ₂  = {!   !} --{!   !} --XF (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
σ , μ ⊨ ϕ₁ W ϕ₂  = {!   !} --{!   !} --XW (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
σ , μ ⊨ ϕ₁ T ϕ₂  = {!   !} --{!   !} --XT (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩

DecidableFormula : ∀ {n} {Γ : Ctx n} → QLTL Γ → Set ℓ
DecidableFormula {_} {Γ} ϕ = {!   !} --∀ ω (a : F₀ (⟦ Γ ⟧*) ω) → Dec (a ∈ ⟨ ϕ ⟩)
