{-
  Syntax for QLTL with negation and all derived operators.
-}
module PNF.QLTL-Full where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)

-- Syntax of full QLTL
data QLTL-Full : ℕ → Set where
  true  : ∀ {n} → QLTL-Full n
  false : ∀ {n} → QLTL-Full n
  !_    : ∀ {n} → QLTL-Full n → QLTL-Full n
  _∧_   : ∀ {n} → QLTL-Full n → QLTL-Full n → QLTL-Full n
  _∨_   : ∀ {n} → QLTL-Full n → QLTL-Full n → QLTL-Full n
  _==_  : ∀ {n} → Fin n  → Fin n  → QLTL-Full n
  _!=_  : ∀ {n} → Fin n  → Fin n  → QLTL-Full n
  ∃<>_  : ∀ {n} → QLTL-Full (suc n) → QLTL-Full n
  ∀<>_  : ∀ {n} → QLTL-Full (suc n) → QLTL-Full n
  ◯_   : ∀ {n} → QLTL-Full n → QLTL-Full n
  A_   : ∀ {n} → QLTL-Full n → QLTL-Full n
  _U_  : ∀ {n} → QLTL-Full n → QLTL-Full n → QLTL-Full n
  _F_  : ∀ {n} → QLTL-Full n → QLTL-Full n → QLTL-Full n
  _W_  : ∀ {n} → QLTL-Full n → QLTL-Full n → QLTL-Full n
  _T_  : ∀ {n} → QLTL-Full n → QLTL-Full n → QLTL-Full n

infix 25 _∧_ _∨_
infix 30 _U_ _F_ _W_ _T_
infix 35 ∃<>_ ∀<>_
infix 40 ◯_ A_ ♢_ □_ ♢*_ □*_
infix 45 !_
infix 50 _==_ _!=_

-- Syntactically defined shorthands
♢_ : ∀ {n} → QLTL-Full n → QLTL-Full n
♢ ϕ = true U ϕ

□_ : ∀ {n} → QLTL-Full n → QLTL-Full n
□ ϕ = ϕ W false

♢*_ : ∀ {n} → QLTL-Full n → QLTL-Full n
♢* ϕ = true F ϕ

□*_ : ∀ {n} → QLTL-Full n → QLTL-Full n
□* ϕ = ϕ T false
