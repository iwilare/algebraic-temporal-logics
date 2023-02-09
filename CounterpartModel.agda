{-# OPTIONS --sized-types #-}

module CounterpartModel {ℓ} where

open import Level using () renaming (suc to sucℓ)
open import Relation.Binary using (REL; Rel)
open import Data.Nat using (ℕ; suc; zero)

open import SortedAlgebra using (Signature; Σ-Algebra; Σ-Rel)

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
    f : ∀ {w₁ w₂}
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
    coinductive
    field
      {B} : W
      rel  : A ⇝ B
      tail : CounterpartTrace B

    Σ-rel = f rel

  open CounterpartTrace public

  -- World of the trace after i steps
  wi : ∀ {A} → ℕ → CounterpartTrace A → W
  wi {A} zero T = A
  wi (suc n) T = wi n (tail T)

  -- Suffix of a trace
  s : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace A) → CounterpartTrace (wi n σ)
  s zero T = T
  s (suc n) T = s n (tail T)
