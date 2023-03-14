{-# OPTIONS --guardedness #-}

{-
  Negation for the temporal operators in full QLTL.
-}
module PNF.Functional.Negation where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Function using (_∘_)
open import Data.Unit using (tt)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)

open import PNF.Functional.Counterpart
open import PNF.Functional.QLTL-Full
open import PNF.Negation
open import Predicates

_≣_ : ∀ {n} → QLTL-Full n → QLTL-Full n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)

◯-negation : ∀ {n} {ϕ : QLTL-Full n} → ! (◯ ϕ) ≣ A (! ϕ)
◯-negation {σ = σ} {μ = μ} = (λ x → ¬∃C→∀C¬ {x = ↑ (C≤ 1 σ) μ} x)
                           , (λ x → ¬∃C←∀C¬ {x = ↑ (C≤ 1 σ) μ} x)

A-negation : ∀ {n} {ϕ : QLTL-Full n} → ! (A ϕ) ≣ ◯ (! ϕ)
A-negation {σ = σ} {μ = μ} = (λ x → ¬∀C→∃C¬ {x = ↑ (C≤ 1 σ) μ} x)
                           , (λ x → ¬∀C←∃C¬ {x = ↑ (C≤ 1 σ) μ} x)

U-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ! (ϕ₁ U ϕ₂) ≣ ! ϕ₂ T (! ϕ₁ ∧ ! ϕ₂)
U-negation {σ = σ} {μ = μ} =
  (λ x → congWeakUntil (λ {i} → ¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → ∀→∩ {x = ↑ (C≤ i σ) μ} (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (∀←∩ {x = ↑ (C≤ i σ) μ} x) in ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} a , ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))

W-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ! (ϕ₁ W ϕ₂) ≣ (! ϕ₂) F (! ϕ₁ ∧ ! ϕ₂)
W-negation {σ = σ} {μ = μ} =
  (λ x → congUntil (λ {i} → ¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → ∀→∩ {x = ↑ (C≤ i σ) μ} (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬weakUntil→until x)) ,
  (λ x → ¬weakUntil←until (congUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (∀←∩ {x = ↑ (C≤ i σ) μ} x) in ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} a , ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))

F-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ! (ϕ₁ F ϕ₂) ≣ (! ϕ₂) W (! ϕ₁ ∧ ! ϕ₂)
F-negation {σ = σ} {μ = μ} =
  (λ x → congWeakUntil (λ {i} → ¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → conjunct∃ {x = ↑ (C≤ i σ) μ} (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil (λ {i} → ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (∃→∩ {x = ↑ (C≤ i σ) μ} x) in ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} a , ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))

T-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ! (ϕ₁ T ϕ₂) ≣ (! ϕ₂) U (! ϕ₁ ∧ ! ϕ₂)
T-negation {σ = σ} {μ = μ} =
  (λ x → congUntil (λ {i} → ¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → conjunct∃ {x = ↑ (C≤ i σ) μ} (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬weakUntil→until x)) ,
  (λ x → ¬weakUntil←until (congUntil (λ {i} → ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (∃→∩ {x = ↑ (C≤ i σ) μ} x) in ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} a , ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))

□-negation : ∀ {n} {ϕ : QLTL-Full n} → ! (□ ϕ) ≣ ♢* (! ϕ)
□-negation {_} {ϕ} {σ = σ} {μ = μ} = ⇒ , ⇐
   where
     ⇒ : σ , μ ⊨ ! (□ ϕ) → σ , μ ⊨ ♢* (! ϕ)
     ⇒ = congUntil (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ _ → tt)
                   (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} proj₁)
       ∘ proj₁ (W-negation {ϕ₁ = ϕ} {ϕ₂ = false} {σ = σ} {μ = μ})

     ⇐ : σ , μ ⊨ ♢* (! ϕ) → σ , μ ⊨ ! (□ ϕ)
     ⇐ = proj₂ (W-negation {ϕ₁ = ϕ} {ϕ₂ = false} {σ = σ} {μ = μ})
       ∘ congUntil (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ _ z → z)
                   (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ z → z , (λ x → x))

♢-negation : ∀ {n} {ϕ : QLTL-Full n} → ! (♢* ϕ) ≣ □ (! ϕ)
♢-negation {_} {ϕ} {σ = σ} {μ = μ} = ⇒ , ⇐
   where
     ⇒ : σ , μ ⊨ ! (♢* ϕ) → σ , μ ⊨ □ (! ϕ)
     ⇒ = congWeakUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → z)
                       (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → proj₁ z tt)
       ∘ proj₁ (F-negation {ϕ₁ = true} {ϕ₂ = ϕ} {σ = σ} {μ = μ})

     ⇐ : σ , μ ⊨ □ (! ϕ) → σ , μ ⊨ ! (♢* ϕ)
     ⇐ = proj₂ (F-negation {ϕ₁ = true} {ϕ₂ = ϕ} {σ = σ} {μ = μ})
       ∘ congWeakUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → z)
                       (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → (λ x → z) , (λ x → z))

□*-negation : ∀ {n} {ϕ : QLTL-Full n} → ! (□* ϕ) ≣ ♢ (! ϕ)
□*-negation {_} {ϕ} {σ = σ} {μ = μ} = ⇒ , ⇐
   where
     ⇒ : σ , μ ⊨ ! (□* ϕ) → σ , μ ⊨ ♢ (! ϕ)
     ⇒ = congUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ _ → tt)
                   ((λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} proj₁))
       ∘ proj₁ (T-negation {ϕ₁ = ϕ} {ϕ₂ = false} {σ = σ} {μ = μ})

     ⇐ : σ , μ ⊨ ♢ (! ϕ) → σ , μ ⊨ ! (□* ϕ)
     ⇐ = proj₂ (T-negation {ϕ₁ = ϕ} {ϕ₂ = false} {σ = σ} {μ = μ})
       ∘ congUntil ((λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ _ z → z))
                   ((λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → z , (λ x → x)))

♢*-negation : ∀ {n} {ϕ : QLTL-Full n} → ! (♢ ϕ) ≣ □* (! ϕ)
♢*-negation {_} {ϕ} {σ = σ} {μ = μ} = ⇒ , ⇐
   where
     ⇒ : σ , μ ⊨ ! (♢ ϕ) → σ , μ ⊨ □* (! ϕ)
     ⇒ = congWeakUntil (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ z → z)
                       ((λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ z → proj₁ z tt))
       ∘ proj₁ (U-negation {ϕ₁ = true} {ϕ₂ = ϕ} {σ = σ} {μ = μ})

     ⇐ : σ , μ ⊨ □* (! ϕ) → σ , μ ⊨ ! (♢ ϕ)
     ⇐ = proj₂ (U-negation {ϕ₁ = true} {ϕ₂ = ϕ} {σ = σ} {μ = μ})
       ∘ congWeakUntil ((λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ z → z))
                       ((λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ z → (λ x → z) , (λ x → z)))
