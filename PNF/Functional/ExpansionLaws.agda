{-# OPTIONS --guardedness #-}

{-
  Negation for the temporal operators in full QLTL.
-}
module PNF.Functional.ExpansionLaws where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Data.Unit
open import Relation.Binary.Definitions
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality using (refl; subst; inspect; sym) renaming ([_] to ≣:_)
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)
open import Data.Vec using (replicate)
open import Relation.Nullary

open import PNF.Functional.Counterpart
open import PNF.Functional.QLTL-Full
open import PNF.Negation
open import Predicates

_≣_ : ∀ {n} → QLTL-Full n → QLTL-Full n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)

U-expansion-law : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ U ϕ₂ ≣ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ U ϕ₂))
U-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ U ϕ₂ → σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ U ϕ₂))
    ⇒ (zero , ϕ₁<i , ϕ₂n) rewrite lift-unit {μ = μ} = inj₁ ϕ₂n
    ⇒ (suc n , (ϕ₁<i , ϕ₂n)) with ϕ₁<i 0 (_≤_.s≤s _≤_.z≤n)
    ... | base rewrite lift-unit {μ = μ} with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ... | nothing | ≣: eq rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                                | ↑-homomorphism {f = rel σ} {g = C≤ n (tail σ)} μ
                                | eq = ⊥-elim ϕ₂n
    ... | just μ′ | ≣: eq = inj₂ (base , n ,
                                         (λ i x → subst (λ p → ∃C∈ p ⇒ _) (sym (switch-tail-suc {σ = σ} {n = i} {μ = μ} eq)) (ϕ₁<i (suc i) (_≤_.s≤s x)))
                                         , subst (λ p → ∃C∈ p ⇒ _) (sym (switch-tail-suc {σ = σ} {n = n} {μ = μ} eq)) ϕ₂n)

    ⇐ : σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ U ϕ₂)) → σ , μ ⊨ ϕ₁ U ϕ₂
    ⇐ (inj₁ x) = 0 , (λ i ()) , a
      where a : ∃C∈ ↑ just μ ⇒ (σ ,_⊨ ϕ₂)
            a rewrite lift-unit {μ = μ} = x
    ⇐ (inj₂ (μ|ϕ₁ , ◯U)) with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ⇐ (inj₂ (μ|ϕ₁ , n , 1<ϕ₁<i , n|ϕ₂)) | just x | ≣: eq =
      suc n , (λ { zero x → lift-exists {μ = μ} μ|ϕ₁
                 ; (suc i) (_≤_.s≤s x) → subst (λ p → ∃C∈ p ⇒ _) (switch-tail-suc {σ = σ} {n = i} {μ = μ} eq) (1<ϕ₁<i i x) })
            , subst (λ p → ∃C∈ p ⇒ _) (switch-tail-suc {σ = σ} {n = n} {μ = μ} eq) n|ϕ₂

F-expansion-law : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ F ϕ₂ ≣ ϕ₂ ∨ (ϕ₁ ∧ A (ϕ₁ F ϕ₂))
F-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ (ϕ₁ F ϕ₂) → σ , μ ⊨ (ϕ₂ ∨ (ϕ₁ ∧ (A (ϕ₁ F ϕ₂))))
    ⇒ (zero , ϕ₁<i , ϕ₂n) rewrite lift-unit {μ = μ} = inj₁ ϕ₂n
    ⇒ (suc n , (ϕ₁<i , ϕ₂n)) with ϕ₁<i 0 (_≤_.s≤s _≤_.z≤n)
    ... | base rewrite lift-unit {μ = μ} with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ... | nothing | ≣: eq = inj₂ (base , tt)
    ... | just μ′ | ≣: eq = inj₂ (base , n ,
                                         (λ i x → subst (λ p → ∀C∈ p ⇒ _) (sym (switch-tail-suc {σ = σ} {n = i} {μ = μ} eq)) (ϕ₁<i (suc i) (_≤_.s≤s x)))
                                         , subst (λ p → ∀C∈ p ⇒ _) (sym (switch-tail-suc {σ = σ} {n = n} {μ = μ} eq)) ϕ₂n)

    ⇐ : σ , μ ⊨ (ϕ₂ ∨ (ϕ₁ ∧ (A (ϕ₁ F ϕ₂)))) → σ , μ ⊨ (ϕ₁ F ϕ₂)
    ⇐ (inj₁ x) = 0 , (λ i ()) , a
      where a : ∀C∈ ↑ just μ ⇒ (σ ,_⊨ ϕ₂)
            a rewrite lift-unit {μ = μ} = x
    ⇐ (inj₂ (μ|ϕ₁ , ◯U)) with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ... | nothing | ≣: eq rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                                 = 1 , (λ { .zero (_≤_.s≤s _≤_.z≤n) → lift-forall {μ = μ} μ|ϕ₁ })
                                     , a
                              where a : ∀C∈ ↑ (C≤ 1 σ) μ ⇒ _
                                    a rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                                            = subst (λ p → ∀C∈ p ⇒ _) (sym eq) (lift-nothing {P = tail σ ,_⊨ ϕ₂})
    ⇐ (inj₂ (μ|ϕ₁ , n , 1<ϕ₁<i , n|ϕ₂)) | just x | ≣: eq =
      suc n , (λ { zero x → lift-forall {μ = μ} μ|ϕ₁
                 ; (suc i) (_≤_.s≤s x) → subst (λ p → ∀C∈ p ⇒ _) (switch-tail-suc {σ = σ} {n = i} {μ = μ} eq) (1<ϕ₁<i i x) })
            , subst (λ p → ∀C∈ p ⇒ _) (switch-tail-suc {σ = σ} {n = n} {μ = μ} eq) n|ϕ₂

W-expansion-law : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ W ϕ₂ ≣ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ W ϕ₂))
W-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ W ϕ₂ → σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ W ϕ₂))
    ⇒ (inj₁ x) with U-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ}
    ... | ⇒ , ⇐ with ⇒ x
    ... | inj₁ x₁ = inj₁ x₁
    ... | inj₂ (ϕ₁ , u) with ↑ (C≤ 1 σ) μ
    ... | just x₁ = inj₂ (ϕ₁ , inj₁ u)
    ⇒ (inj₂ y) with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ... | just x | ≣: eq = inj₂ (subst (λ p → ∃C∈ p ⇒ _) (lift-unit {μ = μ}) (y 0) , inj₂ λ i → subst (λ p → ∃C∈ p ⇒ _) (sym (switch-tail-suc {σ = σ} {n = i} {μ = μ} eq)) (y (suc i)))
    ... | nothing | ≣: eq with ↑ (C≤ 1 σ) μ | y 1
    ... | nothing | ()
    ⇒ (inj₂ y) | nothing | ≣: () | just x | r

    ⇐ : σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ W ϕ₂)) → σ , μ ⊨ ϕ₁ W ϕ₂
    ⇐ (inj₁ x) = inj₁ (0 , (λ i ()) , lift-exists {μ = μ} x)
    ⇐ (inj₂ (ϕ₁μ , u)) with U-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ}
    ... | ⇒ , u⇐ with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ⇐ (inj₂ (ϕ₁μ , inj₁ u)) | ⇒ , u⇐ | just x | ≣: eq = inj₁ (u⇐ (inj₂ (ϕ₁μ , u)))
    ⇐ (inj₂ (ϕ₁μ , inj₂ y)) | ⇒ , u⇐ | just x | ≣: eq = inj₂ a
        where a : ∀ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ _
              a zero = lift-exists {μ = μ} ϕ₁μ
              a (suc i) with y i
              ... | p rewrite switch-tail-suc {σ = σ} {n = i} {μ = μ} eq = p

T-expansion-law : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ T ϕ₂ ≣ ϕ₂ ∨ (ϕ₁ ∧ A (ϕ₁ T ϕ₂))
T-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ T ϕ₂ → σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ A (ϕ₁ T ϕ₂))
    ⇒ (inj₁ x) with F-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ}
    ... | ⇒ , ⇐ with ⇒ x
    ... | inj₁ x₁ = inj₁ x₁
    ... | inj₂ (ϕ₁ , u) with ↑ (C≤ 1 σ) μ
    ... | nothing = inj₂ (ϕ₁ , tt)
    ... | just x₁ = inj₂ (ϕ₁ , inj₁ u)
    ⇒ (inj₂ y) with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ... | nothing | ≣: eq = inj₂ (subst (λ p → ∀C∈ p ⇒ _) (lift-unit {μ = μ}) (y 0) , tt)
    ... | just x | ≣: eq = inj₂ (subst (λ p → ∀C∈ p ⇒ _) (lift-unit {μ = μ}) (y 0) , inj₂ λ i → subst (λ p → ∀C∈ p ⇒ _) (sym (switch-tail-suc {σ = σ} {n = i} {μ = μ} eq)) (y (suc i)))

    ⇐ : σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ A (ϕ₁ T ϕ₂)) → σ , μ ⊨ ϕ₁ T ϕ₂
    ⇐ (inj₁ x) = inj₁ (0 , (λ i ()) , lift-forall {μ = μ} x)
    ⇐ (inj₂ (ϕ₁μ , u)) with F-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ}
    ... | ⇒ , u⇐ with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ⇐ (inj₂ (ϕ₁μ , inj₁ u)) | ⇒ , u⇐ | just x | ≣: eq = inj₁ (u⇐ (inj₂ (ϕ₁μ , u)))
    ⇐ (inj₂ (ϕ₁μ , inj₂ y)) | ⇒ , u⇐ | just x | ≣: eq = inj₂ a
        where a : ∀ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ _
              a zero = lift-forall {μ = μ} ϕ₁μ
              a (suc i) with y i
              ... | p rewrite switch-tail-suc {σ = σ} {n = i} {μ = μ} eq = p
    ⇐ (inj₂ (ϕ₁μ , tt)) | ⇒ , u⇐ | nothing | ≣: eq = inj₂ a
        where a : ∀ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ _
              a zero = lift-forall {μ = μ} ϕ₁μ
              a (suc i) rewrite del-counterparts {σ = σ} {n = i} {μ = μ} eq = tt

♢-expansion-law : ∀ {n} {ϕ : QLTL-Full n} → ♢ ϕ ≣ ϕ ∨ ◯ (♢ ϕ)
♢-expansion-law {_} {ϕ} {_} {σ} {μ} with U-expansion-law {_} {true} {ϕ} {_} {σ} {μ}
... | U⇒ , U⇐ = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ♢ ϕ → σ , μ ⊨ (ϕ ∨ (◯ (♢ ϕ)))
    ⇒ x with U⇒ x
    ... | inj₁ x₁ = inj₁ x₁
    ... | inj₂ (tt , a) = inj₂ a

    ⇐ : σ , μ ⊨ (ϕ ∨ (◯ (♢ ϕ))) → σ , μ ⊨ ♢ ϕ
    ⇐ (inj₁ x) = 0 , (λ i ()) , lift-exists {μ = μ} x
    ⇐ (inj₂ y) = U⇐ (inj₂ (tt , y))

□-expansion-law : ∀ {n} {ϕ : QLTL-Full n} → □ ϕ ≣ ϕ ∧ ◯ (□ ϕ)
□-expansion-law {_} {ϕ} {_} {σ} {μ} with W-expansion-law {_} {ϕ} {false} {_} {σ} {μ}
... | W⇒ , W⇐ = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ □ ϕ → σ , μ ⊨ (ϕ ∧ (◯ (□ ϕ)))
    ⇒ x with W⇒ x
    ... | inj₁ ()
    ... | inj₂ r = r

    ⇐ : σ , μ ⊨ (ϕ ∧ (◯ (□ ϕ))) → σ , μ ⊨ □ ϕ
    ⇐ e = W⇐ (inj₂ e)

♢*-expansion-law : ∀ {n} {ϕ : QLTL-Full n} → ♢* ϕ ≣ ϕ ∨ A (♢* ϕ)
♢*-expansion-law {_} {ϕ} {_} {σ} {μ} with F-expansion-law {_} {true} {ϕ} {_} {σ} {μ}
... | F⇒ , F⇐ = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ♢* ϕ → σ , μ ⊨ (ϕ ∨ (A (♢* ϕ)))
    ⇒ x with F⇒ x
    ... | inj₁ x₁ = inj₁ x₁
    ... | inj₂ (tt , a) = inj₂ a

    ⇐ : σ , μ ⊨ (ϕ ∨ (A (♢* ϕ))) → σ , μ ⊨ ♢* ϕ
    ⇐ (inj₁ x) = 0 , (λ i ()) , lift-forall {μ = μ} x
    ⇐ (inj₂ y) = F⇐ (inj₂ (tt , y))

□*-expansion-law : ∀ {n} {ϕ : QLTL-Full n} → □* ϕ ≣ ϕ ∧ A (□* ϕ)
□*-expansion-law {_} {ϕ} {_} {σ} {μ} with T-expansion-law {_} {ϕ} {false} {_} {σ} {μ}
... | T⇒ , T⇐ = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ □* ϕ → σ , μ ⊨ (ϕ ∧ (A (□* ϕ)))
    ⇒ x with T⇒ x
    ... | inj₁ ()
    ... | inj₂ r = r

    ⇐ : σ , μ ⊨ (ϕ ∧ (A (□* ϕ))) → σ , μ ⊨ □* ϕ
    ⇐ e = T⇐ (inj₂ e)
