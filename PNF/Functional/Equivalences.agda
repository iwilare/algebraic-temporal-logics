{-# OPTIONS --guardedness #-}

{-
  Equivalences for the temporal operators in QLTL.
-}
module PNF.Functional.Equivalences where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (suc; zero; _<′_; _<‴_; _≤‴_; _≤_)
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (subst; inspect; refl; sym) renaming ([_] to ≣:)

open import PNF.Functional.Counterpart
open import PNF.Functional.QLTL-Full

infixl 10 _≣_

_≣_ : ∀ {n} → QLTL-Full n → QLTL-Full n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)

U-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ U ϕ₂ ≣ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂
U-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ U ϕ₂ → σ , μ ⊨ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = inj₁ (n , ϕ₁<i , ϕ₂n) , n , true-before-n , ϕ₂n
      where
        true-before-n : _
        true-before-n i x with ↑ (C≤ i σ) μ | ϕ₁<i i x
        ... | just μ | _ = tt

    ⇐ : σ , μ ⊨ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂ → σ , μ ⊨ ϕ₁ U ϕ₂
    ⇐ (inj₁ u , _) = u
    ⇐ (inj₂ a , n , _ , ϕ₂n) = n , (λ i _ → a i) , ϕ₂n

F-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ F ϕ₂ ≣ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂
F-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ F ϕ₂ → σ , μ ⊨ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = inj₁ (n , ϕ₁<i , ϕ₂n) , n , true-before-n , ϕ₂n
      where
        true-before-n : _
        true-before-n i x with ↑ (C≤ i σ) μ
        ... | nothing = tt
        ... | just μ = tt

    ⇐ : σ , μ ⊨ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂ → σ , μ ⊨ ϕ₁ F ϕ₂
    ⇐ (inj₁ u , _) = u
    ⇐ (inj₂ a , n , _ , ϕ₂n) = n , (λ i _ → a i) , ϕ₂n

W-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ W ϕ₂ ≣ ϕ₁ U ϕ₂ ∨ □ ϕ₁
W-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ W ϕ₂ → σ , μ ⊨ ϕ₁ U ϕ₂ ∨ □ ϕ₁
    ⇒ (inj₁ x) = inj₁ x
    ⇒ (inj₂ y) = inj₂ (inj₂ y)

    ⇐ : σ , μ ⊨ ϕ₁ U ϕ₂ ∨ □ ϕ₁ → σ , μ ⊨ ϕ₁ W ϕ₂
    ⇐ (inj₁ x) = inj₁ x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ϕ₂n))) with ↑ (C≤ n σ) μ
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ()))) | just x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ()))) | nothing
    ⇐ (inj₂ (inj₂ y)) = inj₂ y

T-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ T ϕ₂ ≣ ϕ₁ F ϕ₂ ∨ □* ϕ₁
T-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ T ϕ₂ → σ , μ ⊨ ϕ₁ F ϕ₂ ∨ □* ϕ₁
    ⇒ (inj₁ x) = inj₁ x
    ⇒ (inj₂ y) = inj₂ (inj₂ y)

    ⇐ : σ , μ ⊨ ϕ₁ F ϕ₂ ∨ □* ϕ₁ → σ , μ ⊨ ϕ₁ T ϕ₂
    ⇐ (inj₁ x) = inj₁ x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ϕ₂n))) with ↑ (C≤ n σ) μ | inspect (↑ (C≤ n σ)) μ
    ... | nothing | ≣: eq = inj₁ (n , ϕ₁<i , ∀ϕ₂)
       where ∀ϕ₂ : ∀C∈ ↑ (C≤ n σ) μ ⇒ (s n σ ,_⊨ ϕ₂)
             ∀ϕ₂ rewrite eq = tt
    ⇐ (inj₂ (inj₂ y)) = inj₂ y
