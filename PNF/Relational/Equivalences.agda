{-# OPTIONS --guardedness #-}

{-
  Equivalences for the temporal operators in QLTL.
-}
module PNF.Relational.Equivalences where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (suc; zero; _<′_; _<‴_; _≤‴_; _≤_)
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (subst; inspect; refl; sym) renaming ([_] to ≣:)

open import PNF.Relational.Counterpart
open import PNF.Relational.QLTL-Full

infixl 10 _≣_

_≣_ : ∀ {n} → QLTL-Full n → QLTL-Full n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)

U-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ U ϕ₂ ≣ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂
U-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ U ϕ₂ → σ , μ ⊨ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = inj₁ (n , ϕ₁<i , ϕ₂n) , n
                       , (λ i x → proj₁ (ϕ₁<i i x) , proj₁ (proj₂ (ϕ₁<i i x)) , tt)
                       , ϕ₂n

    ⇐ : σ , μ ⊨ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂ → σ , μ ⊨ ϕ₁ U ϕ₂
    ⇐ (inj₁ u , _) = u
    ⇐ (inj₂ a , n , _ , ϕ₂n) = n , (λ i _ → a i) , ϕ₂n

F-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ F ϕ₂ ≣ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂
F-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ F ϕ₂ → σ , μ ⊨ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = inj₁ (n , ϕ₁<i , ϕ₂n) , n
                       , (λ _ _ _ _ → tt)
                       , ϕ₂n

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
    ⇐ (inj₂ (inj₂ y)) = inj₂ y

T-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ T ϕ₂ ≣ ϕ₁ F ϕ₂ ∨ □* ϕ₁
T-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ T ϕ₂ → σ , μ ⊨ ϕ₁ F ϕ₂ ∨ □* ϕ₁
    ⇒ (inj₁ x) = inj₁ x
    ⇒ (inj₂ y) = inj₂ (inj₂ y)

    ⇐ : σ , μ ⊨ ϕ₁ F ϕ₂ ∨ □* ϕ₁ → σ , μ ⊨ ϕ₁ T ϕ₂
    ⇐ (inj₁ x) = inj₁ x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ϕ₂n))) = inj₁ (n , ϕ₁<i , λ c x → ⊥-elim (ϕ₂n c x))
    ⇐ (inj₂ (inj₂ y)) = inj₂ y
