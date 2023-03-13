{-# OPTIONS --sized-types #-}

module CounterpartModel {ℓ} where

open import Level using () renaming (suc to sucℓ)
open import Relation.Binary using (REL; Rel)
open import Data.Nat using (ℕ; suc; zero)

open import SortedAlgebra using (Signature; Σ-Algebra; Σ-Rel; rel-id; _;_)

record LewisCounterpartModel : Set (sucℓ ℓ) where
  field
    W : Set ℓ
    D : W → Set ℓ
    R : Rel W ℓ
    C : ∀ {w₁ w₂}
      → R w₁ w₂
      → REL (D w₁) (D w₂) ℓ

record CounterpartModel (Σ : Signature {ℓ}) : Set (sucℓ ℓ)  where
  field
    W : Set ℓ
    d : W → Σ-Algebra {ℓ} Σ
    _⇝_ : Rel W ℓ
    𝓒 : ∀ {w₁ w₂}
      → w₁ ⇝ w₂
      → Σ-Rel (d w₁) (d w₂)

record StandaloneCounterpartTrace (Σ : Signature {ℓ}) : Set (sucℓ ℓ)  where
  field
    d : ℕ → Σ-Algebra {ℓ} Σ
    C : ∀ {n} → Σ-Rel (d n) (d (ℕ.suc n))

module _ {Σ : Signature {ℓ}} (M : CounterpartModel Σ) where
  open CounterpartModel M

  record TraceEmbedding (M : CounterpartModel Σ) : Set (sucℓ ℓ) where
    field
      p : ℕ → W
      k : ∀ {n}
        → p n ⇝ p (ℕ.suc n)

  record CounterpartTrace (A : W) : Set (sucℓ ℓ) where
    constructor _⇀_
    coinductive
    field
      {B} : W
      rel  : A ⇝ B
      tail : CounterpartTrace B

    Σ-rel = 𝓒 rel

  open CounterpartTrace public

module _ {Σ : Signature {ℓ}} {M : CounterpartModel Σ} where
  open CounterpartModel M

  open CounterpartTrace

  -- World of the trace after i steps
  wi : ∀ {A} → ℕ → CounterpartTrace M A → W
  wi {A} zero T = A
  wi (suc n) T = wi n (tail T)

  -- Suffix of a trace
  skip : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace M A) → CounterpartTrace M (wi n σ)
  skip zero T = T
  skip (suc n) T = skip n (tail T)

  C≤ : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace M A) → Σ-Rel (d A) (d (wi n σ))
  C≤ zero σ = rel-id
  C≤ (suc n) σ = 𝓒 (rel σ) ; C≤ n (tail σ)
