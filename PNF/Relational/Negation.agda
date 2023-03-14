{-# OPTIONS --guardedness #-}

{-
  Negation for the temporal operators in full QLTL.
-}
module PNF.Relational.Negation where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)

open import PNF.Relational.Counterpart
open import PNF.Relational.QLTL-Full
open import PNF.Negation
open import Predicates

_≣_ : ∀ {n} → QLTL-Full n → QLTL-Full n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)

◯-negation : ∀ {n} {ϕ : QLTL-Full n} → ! (◯ ϕ) ≣ A (! ϕ)
◯-negation = ¬∃C⟶∀C¬ , ¬∃C←∀C¬

U-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ! (ϕ₁ U ϕ₂) ≣ ! ϕ₂ T (! ϕ₁ ∧ ! ϕ₂)
U-negation =
  (λ x → congWeakUntil ¬∃C⟶∀C¬
                       ((λ { (a , b) → ∀→∩ (¬∃C⟶∀C¬ a) (¬∃C⟶∀C¬ b) }))
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil ¬∃C←∀C¬
                                         (λ x → let a , b = ∀←∩ x in ¬∃C←∀C¬ a , ¬∃C←∀C¬ b)
                                         x))

W-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ! (ϕ₁ W ϕ₂) ≣ ! ϕ₂ F (! ϕ₁ ∧ ! ϕ₂)
W-negation =
  (λ x → congUntil ¬∃C⟶∀C¬
                   (λ { (a , b) → λ c x₂ → ¬∃C⟶∀C¬ a c x₂ , ¬∃C⟶∀C¬ b c x₂ })
                    (¬weakUntil→until x))
  , λ x → ¬weakUntil←until (congUntil ¬∃C←∀C¬
                                      (λ { a → ¬∃C←∀C¬ (λ c x₂ x₃ → proj₁ (a c x₂) x₃)
                                             , ¬∃C←∀C¬ (λ c x₂ x₃ → proj₂ (a c x₂) x₃) })
                                      x)
