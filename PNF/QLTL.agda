{-
  Syntax for standard QLTL with negation.
-}
module PNF.QLTL where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)

-- Syntax of QLTL
data QLTL : ℕ → Set where
  true  : ∀ {n} → QLTL n
  !_    : ∀ {n} → QLTL n → QLTL n
  _∨_   : ∀ {n} → QLTL n → QLTL n → QLTL n
  _==_  : ∀ {n} → Fin n  → Fin n  → QLTL n
  ∃<>_  : ∀ {n} → QLTL (suc n) → QLTL n
  ◯_   : ∀ {n} → QLTL n → QLTL n
  _U_  : ∀ {n} → QLTL n → QLTL n → QLTL n
  _W_  : ∀ {n} → QLTL n → QLTL n → QLTL n

infix 25 _∨_
infix 30 _U_ _W_
infix 35 ∃<>_
infix 40 ◯_ ♢_ □_
infix 45 !_
infix 50 _==_

-- Syntactically defined shorthands
♢_ : ∀ {n} → QLTL n → QLTL n
♢ ϕ = true U ϕ

□_ : ∀ {n} → QLTL n → QLTL n
□ ϕ = ϕ W ! true
