module Predicates where

open import Data.Nat using (ℕ; _<_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Relation.Unary using (Pred; _∈_)

-- A holds for all i strictly before n steps
_before_ : ∀ {ℓ} (A : Pred ℕ ℓ) → Pred ℕ ℓ
A before n = ∀ i → i < n → i ∈ A

-- A holds until B is satisfied
_until_ : ∀ {ℓ} (A B : Pred ℕ ℓ) → Set ℓ
A until B = ∃[ n ] (A before n × n ∈ B)

-- A is always satisfied at each step
always : ∀ {ℓ} (A : Pred ℕ ℓ) → Set ℓ
always A = ∀ i → i ∈ A

-- Either until or always hold
_weakUntil_ : ∀ {ℓ} (A B : Pred ℕ ℓ) → Set ℓ
A weakUntil B = A until B ⊎ always A

-- There exists a step after which A is satisfied
eventually : ∀ {ℓ} (A : Pred ℕ ℓ) → Set ℓ
eventually A = ∃[ i ] i ∈ A

-- Implication congruences for until and weak until
congUntil : ∀ {A B A′ B′ : ℕ → Set}
          → (∀ {x} → A x → A′ x)
          → (∀ {x} → B x → B′ x)
          → A until B → A′ until B′
congUntil G F = λ (n , b , t) → n , (λ i x → G (b i x)) , F t

congWeakUntil : ∀ {A B A′ B′ : ℕ → Set}
              → (∀ {x} → A x → A′ x)
              → (∀ {x} → B x → B′ x)
              → A weakUntil B → A′ weakUntil B′
congWeakUntil G F = [ (λ x → inj₁ (congUntil G F x)) , (λ x → inj₂ (λ y → G (x y))) ]
